# Posting the working paper: SSRN, MPRA and Zenodo

What to do, in order, with the text to paste. Read `main.pdf` first: at least the abstract, the theorem
statements (Section 3) and the headline tables (Tables 3–11). Then commit the repository, tag the release,
and post. Everything below is done by you in a browser; nothing is automated.

## 0. Before posting

1. Build the PDF: `paper\build.cmd` (or `bash paper/build.sh`). The output is `paper/main.pdf`.
2. Commit everything and tag the release, for example:
   `git add -A && git commit -m "Working paper v0.1" && git tag -a v0.1 -m "Working paper, preliminary draft"`.
3. If you register an ORCID iD (free, https://orcid.org), add it to your SSRN, MPRA and Zenodo profiles and
   to the title page (`main.tex`, the `\thanks` footnote) before building. It keeps "Manuel Sanchez" and
   "Manuel Antonio Sanchez Garcia" attached to one record.

## 1. Metadata to paste (identical on every platform)

**Title.** Symbolic IV: Discovering Structural Equations under Endogeneity

**Author.** Manuel Sanchez, Independent researcher, manuzrp@gmail.com

**Abstract** (the abstract of `main.pdf`, verbatim, in plain text for pasting):

Symbolic regression finds the formula that best predicts an outcome, so under endogeneity it returns a formula for the conditional mean, not the structural law. This paper scores the formula search with instrumental-variable moment conditions instead: candidate formulas from cheap generators are refitted by GMM on sieve instruments, selected by a GMM model-selection criterion with a structure penalty, and reported with an Anderson–Rubin confidence set over formulas that says whether the data identify the result. The selection rule is consistent for any generator whose candidates contain the true form, with a finite-sample bound that attributes its failures to weak separation or to fitting moment noise, and the confidence set covers the true form without any rank condition. In a Monte Carlo over five designs and five laws, the method recovers the log, power and two-regressor laws in 92–100% of runs under confounding and a heteroskedastic first stage, while the squared-error search never recovers the power law under strong endogeneity, and it flags every weak-instrument run as weakly identified or rejected. On the Engel curves of the 1995 Family Expenditure Survey it reproduces the known Working–Leser and quadratic shapes; on Angrist and Krueger's quarter-of-birth instruments it reports weak identification instead of a formula.

**Keywords.** symbolic regression; instrumental variables; nonparametric IV; GMM model selection; weak
identification

**JEL codes.** C14 (semiparametric and nonparametric methods), C26 (instrumental variables), C52 (model
evaluation, validation and selection)

**Date.** 11 October 2026. **Status.** Working paper, preliminary draft.

**Code and data statement.** Code, run records and replication guide at
https://github.com/manuzrpEd/IV_SymbolicRegression (make the repository public at the same time as the
first preprint, or give the Zenodo DOI instead). Data: public extracts, see REPLICATION.md section 2.

## 2. SSRN (author ID 7169072)

1. Log in at https://hq.ssrn.com, "Submit a paper" ("Submissions" → "Start new submission").
2. Upload `paper/main.pdf`. Title, abstract, keywords, JEL codes as above. Date: the date on the title page.
3. Authors: you are already the submitting author; affiliation "Independent" (SSRN lets you type a free
   affiliation if "Independent researcher" is not in its list).
4. Classification: Econometrics (eJournals: *Econometrics: Econometric & Statistical Methods*,
   *Econometric Modeling: Microeconometric Studies*), and Computer Science / Artificial Intelligence if
   offered. Choose "Working paper" as the paper type and leave "forthcoming/published" blank.
5. Rights: choose the open-access option if offered; otherwise SSRN's default posting licence is fine
   (it is non-exclusive and does not conflict with CC BY on the PDF itself).
6. Submit. SSRN screens new papers within a few days and then assigns the DOI (`10.2139/ssrn.XXXXXXX`).
   Record it: it goes into `CITATION.cff`, the Zenodo record and the next version of the title page.
7. Revisions: "Modify" on the paper's page uploads a new version; earlier versions stay in the record.

## 3. MPRA (user 116109, username manuzrp)

1. Log in at https://mpra.ub.uni-muenchen.de, "Manage deposits" → "New item".
2. Item type: MPRA Paper. Upload `paper/main.pdf` (PDF only).
3. Details: title and abstract as above; **Creators: family name "Sanchez", given name "Manuel"** (the item's
   author field is separate from your profile name, so the paper is attributed as "Sanchez, Manuel"); email
   as you prefer (the profile hides it); Institution: Independent researcher; Language: English;
   Keywords and JEL codes as above (MPRA requires at least one JEL code); Date: 11 October 2026,
   date type "Completion".
4. Deposit. MPRA checks that the paper is an economics working paper and that you are the author, usually
   within one to three working days, then publishes it with a stable URL
   (`https://mpra.ub.uni-muenchen.de/<id>/`) and indexes it in RePEc/IDEAS, which is how economists find it.
5. Revisions: a new version is deposited as a new item linked to the old one ("New version of").

## 4. Zenodo (logged in with GitHub)

Two ways. Both give a DOI and a timestamp; the second needs the repository to be public.

**A. Manual upload (works while the repository is private; can be embargoed).**
1. Produce the archive from the tagged commit, in the repository folder:
   `git archive --format=zip --output=IV_SymbolicRegression-v0.1.zip v0.1`
2. https://zenodo.org → "New upload". Upload the zip and `paper/main.pdf`.
3. Resource type: Software. Title, creators ("Sanchez, Manuel", affiliation Independent researcher),
   description (the abstract plus one line saying the record holds the code, run records and the working
   paper), keywords as above. Licence: MIT (state in the description that `paper/` is CC BY 4.0).
   Version: 0.1. Related works: the SSRN DOI and the MPRA URL once you have them ("is supplemented by").
4. Visibility: "Embargoed" with the date you expect to have reviewed the paper, or "Public" if you post the
   preprint the same day. The DOI exists either way; embargoed files become public automatically on the date.
5. Publish. Zenodo DOIs are permanent; every later version gets its own DOI under one concept DOI.

**B. GitHub integration (automatic from releases; repository must be public).**
1. https://zenodo.org/account/settings/github → switch the repository on.
2. On GitHub, "Releases" → "Draft a new release" from tag v0.1. Zenodo archives it within minutes and
   mints the DOI, reading the metadata from `.zenodo.json` in the repository root.
3. Paste the DOI badge into `README.md` and the DOI into `CITATION.cff`.

## 5. After posting

- Put the SSRN DOI, the MPRA URL and the Zenodo DOI into `CITATION.cff` (`identifiers`), into
  `paper/LICENSE.md` (suggested citation) and into the title-page footnote; rebuild and commit.
- Make the GitHub repository public when the first preprint is live, so that the links in the PDF resolve.
- For a double-blind venue later (NeurIPS, ICML), the submitted PDF must carry no names, acknowledgements
  or links to this repository; use an anonymized copy of the repository for that submission.
