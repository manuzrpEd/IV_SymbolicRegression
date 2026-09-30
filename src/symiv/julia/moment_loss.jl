# Moment criterion Q_n(f) = ||A' r||^2 / n as a PySR `loss_function` (README §6.2, §6.6).
#
# A (n x m) is set from Python before each fit via `symiv_set!` (see symiv/search.py).
# Its rows must line up with dataset.y, so PySR must run with batching=false.
# Constants beyond the bound get a smooth quadratic penalty, so PySR's BFGS
# constant optimizer still works; the hard bound is enforced in the GMM refit.
function symiv_moment_loss(tree, dataset::Dataset{T,L}, options)::L where {T,L}
    prediction, complete = eval_tree_array(tree, dataset.X, options)
    !complete && return L(Inf)
    r = dataset.y .- prediction
    g = Main.SYMIV_A[]' * r
    loss = sum(abs2, g) / length(r)
    bound = Main.SYMIV_BOUND[]
    constants, _ = SymbolicRegression.get_scalar_constants(tree)
    excess = sum(c -> max(abs(c) - bound, zero(c))^2, constants; init=zero(T))
    return L(loss + 1000 * excess)
end
