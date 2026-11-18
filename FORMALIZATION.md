# Approximation Preserving Coresets — Lean 4

Formalization of Milind Prabhu, Chris Schwiegelshohn, and Sudarshan Shyam,
*Approximation Preserving Coresets*, ICML 2026:
https://arxiv.org/abs/2606.17316 (v1, 15 June 2026).

## Final mathematical result

**367 theorem statements are checked, with no placeholders or added axioms.**
The main mathematical approximation-and-size guarantees are now proved:

- An unconditional `(1+ε)` Euclidean APC construction for arbitrary k,
  with a dimension- and input-size-independent inverse-cubic size bound,
  up to one logarithmic factor.
- A fixed summary-only lifting map valid simultaneously for all
  approximation factors and summary solutions, with sampling success
  probability at least 1/2.
- The actual randomized lifting output: for any solver with an α-approximation
  guarantee on the sampled summary, the returned centers are an
  `α(1+ε)`-approximation for the original input with probability at least 1/3.
- An unconditional finite-metric `(4+ε)` APC and final subset-search algorithm,
  with input-independent summary size and a verified FPT candidate count.

**Scope:** the new Euclidean proof uses an alternative iterative sampling
construction. It bypasses the cited general-k strong-coreset theorem; it does
not verify that earlier theorem or the paper's original fast two-stage
implementation. Its concrete proxy uses exhaustive finite support search.
Consequently this project does **not** verify near-linear preprocessing,
full runtime/bit complexity, lower bounds, composability, or experiments.
The older two-stage formalization still has the cited strong-coreset premise.
This is not a claim that every result or algorithmic assertion in the paper
has been formalized.

## Principal final theorems

`APC.EuclideanIteration.euclidean_approximation_preserving_coreset`
proves the unconditional Euclidean summary-size and fixed-lift guarantee.
Its only input hypotheses are a nonempty finite positively weighted input,
a nonempty finite center-index type, a real inner-product ambient space,
and `0<ε≤1`. No strong-coreset, concentration, proxy-approximation, or
geometric-lifting theorem is supplied as a premise.

`APC.EuclideanIteration.euclidean_randomized_apc` proves the same explicit
size bound and the approximation guarantee for the centers actually returned
by randomized lifting. The solver may depend on the entire sampling history.
Its stated α-approximation guarantee on each final summary is the expected
solver premise; the coreset construction and lifting probability are proved.

`APC.MetricIteration.finite_metric_subset_enumeration_correctness`
proves the finite-metric construction, exact-size subset solver, returned
`(4+ε)` approximation with failure at most 1/2, and an explicit parameter-only
binomial candidate bound. Exact finite ambient proxies remove oracle premises;
their efficient implementation is outside the runtime verification.

## Euclidean construction and explicit size

Let k be the positive center-tuple length, N the positive input entry count,
and `0<ε≤1`. Set

```
t = ceil(30/ε) + 1 ≤ 32/ε
k' = t k
B = 14400
L_i = max(log^(i+1) N, B)
e_i = ε / sqrt(L_i).
```

Stop after the least positive iteration index n with `log^(n) N≤B`.
At each step, run the proved four-component sensitivity sampler on the
preceding weighted cloud. Use the prescribed positive integer count

```
m_(i+1) = metricStageSampleCount(k', m_i, 4, e_i, δ_i),
```

where `m_0=N`, `δ_0=1/(4N)`, and later failure budgets use the preceding
level's rounded square, exactly as `MetricIteration.scheduledFailure`.
The stage proxy is the best center tuple supported on that stage's input.
This proxy has a verified factor-four guarantee for all ambient queries;
its exhaustive computation is deliberately not described as near-linear.

Each local event preserves the finite family of k-tuples of means of t
points in that stage's input, plus one fixed original optimum. The sampler
never uses that optimum: it is only a proof reference. Every mean witness
from the final sample is a witness in every preceding input because sampled
supports are nested. Thus costs of all possible lifted outputs and the
reference optimum transfer through the entire chain.

Lean proves

```
Σ_i e_i ≤ ε/40,       Σ_i δ_i ≤ 1/2.
```

It also proves existence of an exact original optimum by a finite search over
cluster assignments and their weighted centroids, including empty clusters.
No compactness, finite ambient dimension, or optimum-existence premise is
needed for the final Euclidean theorem.

For the final draw count m, define

```
J = 643464225 k / ε³
U(k,ε) = exp(16) J (1+log J) · 14400².
```

The final theorems prove `m≤U(k,ε)`. This is an exact inverse-cubic bound
with one logarithmic factor, not a formal Lean soft-O notation statement.
The constants are conservative. Every retained point comes from the original
input, and every sampled weight is strictly positive on every history.
Repeated draws are separate weighted entries; aggregation identities in the
project preserve objective values when equal locations are merged.

The fixed lifting map uses only the final summary and its input solution,
not the original input, optimum, or approximation factor. The randomized
version uses the already verified cluster-sampling law, t-point means,
best-trial selection and repetition count `clog_3(3k)+1`. The sharp conditional
probability bound combines sampling success ≥1/2 with conditional lifting
success ≥2/3, yielding overall returned-center success ≥1/3. No unconditional
independence between the sampler, solver and lifting law is assumed.

## Metric construction and subset enumeration

For fixed proxy factor a, let

```
D = 23+22a
R = 4(64a+8a²)
H = [1+48k+R(1+k)] D² / ε²
Γ = exp(16) H (1+log H).
```

The actual recursive metric counts satisfy `m_(i+1)≤Γ L_i²`, and the terminal
count is at most `Γ·14400²`, independently of N. The final solver enumerates
size-k subsets of sampled indices and returns a minimum-cost one. Lean
proves the sample count is at least k, even when the original input has fewer
than k entries. Any repeated tuple can be covered by a size-k subset without
increasing nearest-center cost.

The search has exactly `choose(m,k)` index-set candidates. The elementary
exponential-series estimate proves

```
choose(m,k) ≤ (e m/k)^k.
```

For exact proxies, `H=2025(289+336k)/ε²`, and the actual terminal candidate
count is bounded by

```
[exp(17)·1265625·14400²·(1+log H)/ε²]^k.
```

This verifies the binomial reduction, its FPT parameter dependence, and the
correctness of the same subset solver's returned centers. It is a candidate
count, not a complete running-time theorem.

## Other verified results and original construction

The finite-family concentration theorem is proved from exponential moments,
Bernstein concentration, importance sampling, normalized sensitivity laws,
near/far cluster geometry, structural events and finite union bounds. Its
sufficient sampling budgets are explicit.

The original two-stage Euclidean route, including randomized lifting and
variable-size random first-stage composition, is also checked **conditional
on** a supplied strong first summary. Substitution of any supplied polynomial
first-stage size gives explicit inverse-cubic final sample bounds. The cited
general-k strong-input construction itself has not been independently verified.
This dependence is absent from the new iterative final theorems.

Independent unconditional constructions are also verified for one-center
Euclidean strong coresets and general-k finite-ambient strong coresets.
The one-center count is `ceil(144/ε²)+1`, with success ≥2/3 including exact
zero-variance behavior. In an n-point finite ambient metric, the exact-proxy
strong count is bounded by

```
680400 k [log(8k/δ)+log n]/ε² + 2,
```

or, when `k≤n`, by `1360800 k [log(8/δ)+log n]/ε²+2`.

## Verified modules

| Component | Main module |
|---|---|
| Weighted centroid, variance identity, mean minimization | `Geometry` |
| Supported small-sample mean existence and weighted random mean estimate | `SmallMean`, `RandomMean` |
| Independent product draws, repetition, union bounds | `FiniteProbability`, `Amplification` |
| Bernstein bound proved from exponential moments | `Bernstein` |
| Importance estimator, centering, moments, tail bounds | `ImportanceSampling` |
| Metric distance-to-centers and residual geometry | `ConcentrationGeometry` |
| Close residual moments and concentration | `ResidualSampling`, `ResidualFamily`, `KMeansResidual` |
| Logarithmic finite-family budgets | `SamplingBudgets`, `WitnessBudget` |
| Sampled k-means objective and aggregation identities | `Sampler`, `Aggregation` |
| Proxy-cluster partitions and sum identities | `Partition`, `PartitionGeometry` |
| Normalized four-component sampler and all four lower bounds | `SensitivityDistribution` |
| Structural sampling events, including zero cluster cost | `StructuralSampling` |
| Far-cluster stability and deterministic global error assembly | `FarClusters`, `GlobalError` |
| Full global probability bound and standard relative-error guarantee | `GlobalSampling`, `FiniteFamilyCoreset` |
| Witness counts, lifting, two-stage transfer, fixed lifting map | `Witnesses`, `Lifting`, `TwoStage`, `Guarantee` |
| Probabilistic Euclidean compression and explicit sample counts | `EuclideanCompression`, `SampleCounts` |
| Best sampled mean, amplified failure, zero-mass fallback | `BestMean` |
| Product marginals and conditional probability composition | `ProductProbability` |
| Joint randomized lifting output and witness membership | `RandomLifting`, `LiftingCounts` |
| Approximation guarantee for the actual randomized output | `RandomizedTransfer` |
| Coreset sampling, adaptive solver, randomized lifting, explicit counts | `RandomizedCompression`, `RandomizedCounts` |
| Metric rounding and conditional `(4+ε)` transfer | `Clustering`, `Metric` |
| Variable-error telescoping and nested supports | `Iteration` |
| Adaptive laws, including changing finite outcome types | `AdaptiveIteration`, `AdaptiveProbability` |
| Metric witness counting and explicit local sampler | `MetricSampling`, `MetricStageKernel` |
| Least log stopping index and uniform error budget | `LogSchedule` |
| Rounded paper counts, terminal size, failure-budget summability | `MetricSchedule` |
| Actual adaptive sampler, positive weights, returned centers | `IteratedMetricSampling` |
| Full log stopping and recursive-count output guarantee | `MetricLogCompression` |
| Finite-metric returned-center correctness without a proxy premise | `MetricRoundedCompression` |
| Actual recursive count envelope and input-independent final draw bound | `MetricSize` |
| Distinct support bound and joint size/correctness theorem | `MetricSizeCorrectness` |
| Exact Euclidean size substitution for both witness lengths | `EuclideanSize` |
| Conditional laws with outcome-dependent finite sample spaces | `DependentKernel` |
| Random first-stage size/accuracy composition for actual centers | `RandomStrongInput` |
| All-center preservation from three moment estimates | `OneCenterMoments` |
| Exact scalar and vector importance-estimator moments | `ImportanceMoments` |
| Centroid-based sensitivity law, bounds and sampled moment identities | `OneCenterSampling` |
| Joint moment error and uniform one-center concentration | `OneCenterStrong` |
| Unconditional k=1 construction, explicit count and zero variance | `OneCenterConstruction` |
| Center-tuple interface and supported coreset existence | `OneCenterCorollaries` |
| Unconditional finite-ambient strong coresets and exact size bounds | `FiniteMetricStrong` |
| Final support search, returned solution correctness and candidate counts | `MetricEnumeration` |
| Exact-size subset solver, coverage of repeated tuples and binomial count | `SubsetSearch` |
| Sufficient draw count, factorial cancellation and FPT candidate envelope | `BinomialBudget` |
| Actual subset-search output and probability guarantee for the sampler | `MetricSubsetEnumeration` |

| Exact Euclidean optimum from finite cluster assignments | `EuclideanOptimum` |
| Local preservation of mean witnesses without strong coresets | `EuclideanStage` |
| Actual Euclidean iterative sampler and nested witness transfer | `EuclideanIteration` |
| Unconditional arbitrary-k Euclidean APC guarantee | `EuclideanCompletion` |
| Sharp conditional success-probability composition | `SharpKernel` |
| Actual randomized returned centers after Euclidean iteration | `EuclideanRandomCompletion` |
| Explicit inverse-cubic size and final theorem statements | `EuclideanCubicSize` |

## Remaining scope

- Verify the paper's original fast two-stage preprocessing, including its
  cited general-k strong-coreset primitive, if that exact algorithm is desired.
  This is no longer a dependency of the completed iterative Euclidean
  approximation-and-size theorem.
- Supply executable arithmetic/oracle implementations and full operation or
  bit-complexity bounds. In particular, exhaustive preprocessing proxies do
  not establish the claimed near-linear input dependence.
- Formalize lower bounds, composability, experiments, and other claims outside
  the upper-bound approximation-and-size arguments.
- Optionally add Lean `IsBigO`/soft-O notation theorems or optimize constants.
  The explicit scalar size and enumeration inequalities are already proved.

## Interactive file dependency graph

Open [the offline interactive graph](dependency-graph/apc-dependency-graph.html)
to explore all 72 proof files, search the 367 checked theorems, and inspect the
Lean source. The graph follows the PFR blueprint's green checked-node style.
Arrows show file imports, not kernel-level lemma dependencies. Filtered views
trace the Euclidean, metric, and original conditional two-stage routes.

A [vector PDF](dependency-graph/apc-file-dependencies.pdf), SVG, raw import data
and regeneration scripts are included. See [graph notes](dependency-graph/README.md)
for the exact scope and rebuilding instructions.

## Build and audit

Pinned versions: Lean `v4.24.0`; mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

With elan/lake installed and network access:

```sh
bash bootstrap.sh
bash check.sh
```

`check.sh` builds every source module through Lake, checks the full
import chain, and audits every named theorem. The archive excludes build
caches. `final-audit.log` records the axiom audit, and
`verification-summary.json` records the checked source hashes and count.

Every audited theorem uses only Lean's standard classical foundations:
`propext`, `Classical.choice`, and `Quot.sound`. There are no placeholders,
added axioms, or disabled proof checks.
