module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.ColsMinSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AcycSimp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.LogLeExp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TorsBoundPow

@[expose] public section

open NumberField Matrix UpperTheory.V

namespace UpperTheory.V.KT

theorem sx_exact (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N m : ℕ) :
    KH.FaceExactTo (Sx L N) (Sx.face L N) m := by
  obtain ⟨h1, h2, h3⟩ := ConeExtensionAcyclic.acyc_simp (good L N)
  exact KH.tupExact _ _ h1 (by rw [h2]; exact Set.univ_nonempty) h3 m

theorem orbBound_mono (L : Type) [Field L] [NumberField L] (N : ℕ) {p p' : ℕ} (h : p ≤ p') :
    orbBound L N p ≤ orbBound L N p' := by
  unfold orbBound
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) ?_)
  exact Nat.mul_le_mul_left _ (by omega)

theorem tors_le (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N m : ℕ) :
    KH.TorsLe (K.HGL L N m) (KH.bound m (orbBound L N m) (3 ^ (dd L N * N)) (m + 2)) :=
  KH.mainFace (Gm L N) (Sx L N) (Sx.face L N) Sx.face_smul m _ _ (Nat.one_le_pow _ _ (by norm_num))
    (sx_exact L N m)
    (fun p hp => ⟨(orb L N p).1, (orb L N p).2.trans (orbBound_mono L N hp)⟩)
    (fun p _ => stab L N p)

end UpperTheory.V.KT
