# The projective curve and its Jacobian

Let $`s`$ be a rational parameter outside the six contacts and let $`d`$ be a nonzero rational twist. The smooth projective curve completing the Picard sextic has genus two. Over $`L=\mathbb Q(\sqrt{-2},\sqrt{-3})`$, its Jacobian is isomorphic, as a commutative group scheme, to each Galois pullback. The theorem `family_galois_pullback` uses the two affine charts of the proper curve to identify ordinary coefficient conjugation with base change on the Jacobian. [Proof](../Lean/Lemmas/picard-application/PicardDescent.lean) · [Role in the height argument](../picard/README.md)

For each prime $`p\gt 3`$ of even contact, the global twisted Jacobian also agrees after scalar extension with the proper-completion Jacobian of the integral sextic over the finite unramified local field. [Local comparison](../Lean/Lemmas/picard-application/PicardLocalization.lean) · [Application of the reduction criterion](../Lean/Lemmas/picard-application/PicardGoodReduction.lean)

The qualitative theorem derives one polynomial defining the integers from the listed general Prym, descent, period, height, reduction and rank statements. Its proof identifies the actual Jacobians, the finite exceptional set and the common descent field. A companion calculation gives the coefficient matrix and change of variables in the genus-two Prym isogeny. [Final theorem](../Lean/Lemmas/picard-application/PicardConclusion.lean) · [Prym coordinate calculation](../Lean/Lemmas/picard-application/PrymCoordinates.lean) · [Sources and hypotheses](../docs/qualitative-existence.md) · [Verified declarations](../picard/verification.json)

The preparation command collects 147 project modules and fetches 21 files from the pinned Tau Ceti revision. It verifies every SHA-256 digest and copies the Tau Ceti license. An existing Tau Ceti checkout can be supplied with `--tau-ceti`. The Lake manifest pins NYLL, the upstream arithmetic development and Mathlib. Run these commands from the root of the source edition with Lean 4.35.0 and Python 3.11 or newer. Choose a fresh destination for the prepared project.

```sh
python3 geometry/prepare.py ../picard-geometry-build
cd ../picard-geometry-build
lake exe cache get
lake build +PicardConclusion:olean +PrymCoordinates:olean
```

The arithmetic and height package builds separately. [Source inventory](sources.json) · [Pinned dependencies](lake-manifest.json) · [Tau Ceti license](vendor/LICENSE)
