"""DeepIV (Hartford et al. 2017) for one positive regressor (README §8.1). Needs the `deep` extra (torch).

Stage 1: a mixture density network for log x given z. Stage 2: a network h fit so
that the average of h over draws from stage 1 predicts y. Returns a callable, no formula.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from symiv.criteria.instruments import as_2d


@dataclass
class DeepIV:
    net: object  # torch module on standardized log x
    t_mean: float
    t_sd: float
    y_mean: float
    y_sd: float

    def __call__(self, X: np.ndarray) -> np.ndarray:
        import torch

        t = (np.log(as_2d(X)) - self.t_mean) / self.t_sd
        with torch.no_grad():
            out = self.net(torch.as_tensor(t, dtype=torch.float32)).numpy()[:, 0]
        return out * self.y_sd + self.y_mean


def fit_deepiv(
    X: np.ndarray,
    y: np.ndarray,
    Z: np.ndarray,
    seed: int = 0,
    components: int = 5,
    hidden: int = 64,
    samples: int = 10,
    batch: int = 128,
    lr: float = 1e-3,
    max_epochs: int = 300,
    patience: int = 20,
    threads: int = 4,
) -> DeepIV:
    import torch
    from torch import nn

    torch.manual_seed(seed)
    torch.set_num_threads(threads)
    rng = np.random.default_rng(seed)

    t = np.log(as_2d(X))
    t_mean, t_sd = float(t.mean()), float(t.std())
    y_mean, y_sd = float(y.mean()), float(y.std())
    z = as_2d(Z)
    z = (z - z.mean(0)) / np.where(z.std(0) > 0, z.std(0), 1.0)
    T = torch.as_tensor((t - t_mean) / t_sd, dtype=torch.float32)
    Zt = torch.as_tensor(z, dtype=torch.float32)
    Y = torch.as_tensor((y - y_mean) / y_sd, dtype=torch.float32)

    perm = rng.permutation(len(y))
    val, train = perm[: len(y) // 5], perm[len(y) // 5 :]

    def mlp(d_in, d_out):
        return nn.Sequential(nn.Linear(d_in, hidden), nn.ReLU(), nn.Linear(hidden, hidden), nn.ReLU(), nn.Linear(hidden, d_out))

    # Stage 1: mixture density network for t | z.
    mdn = mlp(Zt.shape[1], 3 * components)

    def mixture(zb):
        logits, mu, log_sigma = mdn(zb).chunk(3, dim=1)
        return logits, mu, log_sigma.clamp(-7, 3)

    def nll(idx):
        logits, mu, log_sigma = mixture(Zt[idx])
        comp = torch.distributions.Normal(mu, log_sigma.exp()).log_prob(T[idx])
        return -torch.logsumexp(torch.log_softmax(logits, 1) + comp, 1).mean()

    _train(mdn.parameters(), nll, train, val, batch, lr, max_epochs, patience, rng, [mdn])

    def draw(idx, gen):  # samples x len(idx) draws of t from stage 1
        with torch.no_grad():
            logits, mu, log_sigma = mixture(Zt[idx])
            k = torch.multinomial(torch.softmax(logits, 1), samples, replacement=True, generator=gen)  # len x samples
            eps = torch.randn(k.shape, generator=gen)
            return (mu.gather(1, k) + log_sigma.exp().gather(1, k) * eps).T

    # Stage 2: h(t) such that the mean of h over stage-1 draws predicts y.
    h = mlp(1, 1)
    gen = torch.Generator().manual_seed(seed)
    fixed_val_draws = draw(val, gen)

    def loss(idx):
        draws = fixed_val_draws if idx is val else draw(idx, gen)
        pred = h(draws.reshape(-1, 1)).reshape(draws.shape).mean(0)
        return ((Y[idx] - pred) ** 2).mean()

    _train(h.parameters(), loss, train, val, batch, lr, max_epochs, patience, rng, [h])
    return DeepIV(h, t_mean, t_sd, y_mean, y_sd)


def _train(params, loss_fn, train, val, batch, lr, max_epochs, patience, rng, modules):
    """Adam with early stopping on the validation loss; restores the best weights."""
    import copy

    import torch

    params = list(params)
    opt = torch.optim.Adam(params, lr=lr)
    best, best_state, bad = np.inf, None, 0
    for _ in range(max_epochs):
        order = rng.permutation(train)
        for start in range(0, len(order), batch):
            opt.zero_grad()
            loss_fn(order[start : start + batch]).backward()
            opt.step()
        with torch.no_grad():
            v = float(loss_fn(val))
        if v < best - 1e-6:
            best, best_state, bad = v, [copy.deepcopy(m.state_dict()) for m in modules], 0
        else:
            bad += 1
            if bad >= patience:
                break
    for m, state in zip(modules, best_state):
        m.load_state_dict(state)
