# breakthroughs

Autonomous AI research sessions that try to make an original mathematical
discovery. Each dated directory is one session: an AI agent (Claude, running
in Claude Code) picks open problems, attacks them with math and computation,
verifies everything independently, checks the literature for novelty the same
day, and writes up whatever survived — including the failures.

The target pool so far is [Erdős problems](https://www.erdosproblems.com/),
using [Tao's database](https://github.com/teorth/erdosproblems) to find open
problems that a finite computation could in principle resolve.

## Ground rules

- **Nothing is claimed without verification.** Every witness is re-checked by
  independent implementations (usually 3–4); every SAT result carries a
  DRAT certificate checked with drat-trim or solver-independent replication.
- **Novelty is checked before claiming, not after.** Same-day literature
  search on every result. When this check fails, the attack is aborted and
  the postmortem is kept (see `p617` in the first session — resolved by four
  parallel AI efforts days before we got there).
- **Negative results are recorded honestly**: search-frontier extensions,
  refuted ansätze, and evidence *for* conjectures are deliverables too.
- These are **unrefereed research notes produced with heavy AI assistance**.
  Read them the way you'd read a preprint from a stranger: the certificates
  and reproduce steps are there so you don't have to trust anyone.

## Sessions

### [2026-07-24 — Erdős problem attack](2026-07-24-erdos-attack/)

Six open problems attacked in parallel. Highlights:

- **Erdős #835** (chromatic number of the Johnson graph J(20,10), the first
  open case): new computer-proved, DRAT-certified theorem — *no proper
  11-colouring of J(20,10) admits any order-11 symmetry*. Any witness for
  χ = 11, if one exists, is 11-asymmetric, ruling out the natural algebraic
  constructions. ([`p835/LEMMA.md`](2026-07-24-erdos-attack/p835/LEMMA.md))
- **Erdős #993** (unimodality of tree independence polynomials): exhaustive
  verification for all 8.69 billion trees on ≤ 29 vertices (independent
  replication of the existing record), plus the **first census of
  non-log-concave trees at n = 29** (exactly 7; smallest odd order), a
  not-in-OEIS census sequence, and an empirical margin law ⌊2n/3⌋.
- **Erdős #647**: no witness below 3.5×10¹² (direct sieve, 3.5× past the
  OEIS-recorded frontier) + independent audit of an unpublished certificate
  reaching 6×10¹⁷.
- **Erdős #488**: improved constant in Tao's asymptotic regime
  (1.0311 → 1.0883) and a sharpened conjectural form of the inequality.
- **Erdős #97, #106**: no counterexamples; new structural reductions and
  quantitative evidence for the conjectured answers.
- **Erdős #617**: aborted after the novelty check — a case study in the
  July 2026 AI gold rush on Erdős problems.

Full details, code, witnesses, and certificates:
[session README](2026-07-24-erdos-attack/README.md).
