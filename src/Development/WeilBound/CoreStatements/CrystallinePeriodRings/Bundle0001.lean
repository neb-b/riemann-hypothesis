module

public import Mathlib
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.CrystallinePeriodRings.FrobAinfMapFrobenius
section
noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

section Abstract

theorem frob_injective_of_fac {A B E : Type} [CommRing A] [CommRing B] [Field E] {F : B →+* E}
    {f : A →+* B} {g : A →+* E} (h : Fac F f g) (hg : Function.Injective g) :
    Function.Injective f := fun x y e => hg (by rw [← h, ← h, e])

theorem frob_fix_padic {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] (F : B →+* B)
    (q : ℚ_[l] →+* B) (h : ∀ z : ℤ_[l], F (q (z : ℚ_[l])) = q (z : ℚ_[l])) (x : ℚ_[l]) :
    F (q x) = q x :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (S := ℚ_[l])
    (j := F.comp q) (k := q) (RingHom.ext h)) x

theorem frob_map_mul_natCast {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n : ℕ) (x : A) :
    f ((n : A) * x) = (n : B) * f x := by
  rw [map_mul, map_natCast]

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem frob_oD_apply (x : Om l) :
    oD l x = algebraMap (Per6.BdRp l) (Per6.BdR l) (algClToBdR l x) := rfl

theorem frob_qB_coe (z : ℤ_[l]) : qB l (z : ℚ_[l]) = Per6.cB l (algebraMap (AInf ℂ_[l] l)
    (ACris.ACris ℂ_[l] l) (IsPerfectoidField.padicIntToWitt l z)) := by
  apply ιCD_injective
  refine (ιCD_qB _).trans (Eq.trans ?_ (ιCD_cB _).symm)
  rw [cD_apply, ACris.iota_padicInt, frob_oD_apply, AlgHom.commutes]

theorem frob_phi_padicInt (z : ℤ_[l]) :
    ACris.phi (K := ℂ_[l]) (p := l) (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)
      (IsPerfectoidField.padicIntToWitt l z)) =
    algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (IsPerfectoidField.padicIntToWitt l z) := by
  rw [ACris.phi_algebraMap, ACris.frobenius_padicIntToWitt]

theorem φB_qB (q : ℚ_[l]) : Per6.φB l (qB l q) = qB l q :=
  frob_fix_padic (Per6.φB l) (qB l) (fun z =>
    (congrArg (Per6.φB l) (frob_qB_coe z)).trans (((φB_cB _).trans
      (congrArg (Per6.cB l) (frob_phi_padicInt z))).trans (frob_qB_coe z).symm)) q

theorem frob_phi_tA :
    ACris.phi (K := ℂ_[l]) (p := l) (Per6.tA l) = (l : ACris.ACris ℂ_[l] l) * Per6.tA l :=
  ACris.phi_periodT_eq_mul (untilt_epsilon (p := l))

theorem φB_tB : Per6.φB l (tB l) = (l : Per6.Bcris l) * tB l :=
  ((φB_cB (Per6.tA l)).trans (congrArg (Per6.cB l) frob_phi_tA)).trans
    (frob_map_mul_natCast (Per6.cB l) l (Per6.tA l))

theorem frob_cB_injective : Function.Injective (Per6.cB l) :=
  frob_injective_of_fac (ιCD_fac l) (cD_injective l)

theorem frob_aB_apply (a : Ainf l) : Per6.aB l a =
    Per6.cB l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Per6.ainfMap l a)) :=
  (RingHom.comp_apply _ _ a).trans (RingHom.comp_apply _ _ _)

theorem frob_coeff_tiltMap (xb : OCb l) (k : ℕ) (y : OC l)
    (h : PreTilt.coeff k xb = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    PreTilt.coeff k (Per6.tiltMap l xb) = Ideal.Quotient.mk _ (Per6.intEquiv l y) :=
  (show PreTilt.coeff k (Per6.tiltMap l xb) = Per6.modPEquiv l (PreTilt.coeff k xb) from rfl).trans
    ((congrArg (Per6.modPEquiv l) h).trans rfl)

theorem frob_ainfMap_teich (xb : OCb l) :
    Per6.ainfMap l (WittVector.teichmuller l xb) = WittVector.teichmuller l (Per6.tiltMap l xb) :=
  WittVector.map_teichmuller l _ _

theorem frob_ainfMap_frobenius (a : Ainf l) :
    Per6.ainfMap l (WittVector.frobenius a) = WittVector.frobenius (Per6.ainfMap l a) := by
  ext n
  simp [Per6.ainfMap, WittVector.map_coeff, WittVector.coeff_frobenius_charP]

theorem frob_phi_ainfMap (a : Ainf l) :
    algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Per6.ainfMap l (WittVector.frobenius a)) =
      ACris.phi (K := ℂ_[l]) (p := l)
        (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Per6.ainfMap l a)) := by
  rw [ACris.phi_algebraMap, frob_ainfMap_frobenius]
  rfl

theorem aB_frobenius (a : Ainf l) : Per6.aB l (WittVector.frobenius a) = Per6.φB l (Per6.aB l a) :=
  ((frob_aB_apply _).trans (congrArg (Per6.cB l) (frob_phi_ainfMap a))).trans
    ((φB_cB _).symm.trans (congrArg (Per6.φB l) (frob_aB_apply a).symm))

end PositivityTheory.LocInh
end
end

-- bundled from Development.WeilBound.CoreStatements.CrystallinePeriodRings.PhiGalCris
section
noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GaloisCommutant

section Abstract

variable {A B E : Type} [CommRing A] [CommRing B] [CommRing E] {a t : A} {f : A →+* B}

theorem comm_equiv (hf : IsFrac f a t) (ι : B →+* E) (s : B →+* B) (d : E ≃+* E)
    (e : ∀ x, ι (s (f x)) = d (ι (f x))) (b : B) : ι (s b) = d (ι b) :=
  RingHom.congr_fun (hf.hom_ext (g := ι.comp s) (h := (d : E →+* E).comp ι) e) b

theorem comm_self (hf : IsFrac f a t) (u s : B →+* B)
    (e : ∀ x, u (s (f x)) = s (u (f x))) (b : B) : u (s b) = s (u b) :=
  RingHom.congr_fun (hf.hom_ext (g := u.comp s) (h := s.comp u) e) b

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem toBot_one : Per6.toBot (1 : GQ l) = 1 := AlgEquiv.ext fun _ => rfl

theorem toBot_mul (g h : GQ l) : Per6.toBot (g * h) = Per6.toBot g * Per6.toBot h :=
  AlgEquiv.ext fun _ => rfl

theorem σD_eq (g : GQ l) : Per6.σD g = galBdRField (Per6.toBot g) := rfl

theorem σD_eq_smul (g : GQ l) (x : Per6.BdR l) : Per6.σD g x = Per6.toBot g • x := by
  rw [σD_eq, gal_smul_bDeRham_def]

theorem σD_algebraMap (g : GQ l) (y : Per6.BdRp l) :
    Per6.σD g (algebraMap (Per6.BdRp l) (Per6.BdR l) y) =
      algebraMap (Per6.BdRp l) (Per6.BdR l) (Per6.toBot g • y) := by
  rw [σD_eq, galBdRField_algebraMap]

theorem cD_galCris (g : GQ l) (x : ACris.ACris ℂ_[l] l) :
    cD l (ACris.galCris (Per6.toBot g) x) = Per6.σD g (cD l x) := by
  rw [cD_apply, cD_apply, σD_algebraMap, ← ACris.gal_smul_def, ACris.iota_gal_smul]

theorem ιCD_σB_aux (g : GQ l) (b : Per6.Bcris l) : ιCD l (Per6.σB g b) = Per6.σD g (ιCD l b) :=
  comm_equiv (cB_isFrac l) _ _ _ (fun x =>
    ((congrArg (ιCD l) (σB_cB g x)).trans (ιCD_cB _)).trans
      ((cD_galCris g x).trans (congrArg (Per6.σD g) (ιCD_cB x).symm))) b

theorem σD_one_aux (b : Per6.BdR l) : Per6.σD (1 : GQ l) b = b := by
  rw [σD_eq_smul, toBot_one, one_smul]

theorem σD_mul_aux (g h : GQ l) (b : Per6.BdR l) :
    Per6.σD (g * h) b = Per6.σD g (Per6.σD h b) := by
  rw [σD_eq_smul, σD_eq_smul, σD_eq_smul, toBot_mul, mul_smul]

theorem oD_apply (x : Om l) :
    oD l x = algebraMap (Per6.BdRp l) (Per6.BdR l) (algClToBdR l x) := rfl

theorem phi_galCris (g : GQ l) (x : ACris.ACris ℂ_[l] l) :
    ACris.phi (K := ℂ_[l]) (p := l) (ACris.galCris (Per6.toBot g) x) =
      ACris.galCris (Per6.toBot g) (ACris.phi (K := ℂ_[l]) (p := l) x) := by
  rw [← ACris.gal_smul_def, ← ACris.gal_smul_def, ACris.phi_gal_smul]

theorem coe_χQ (g : GQ l) :
    ((χQ l g : ℚ_[l]ˣ) : ℚ_[l]) = ((cycloChar ⊥ (Per6.toBot g) : ℤ_[l]) : ℚ_[l]) := rfl

theorem cD_χA (g : GQ l) : cD l (Per6.χA (Per6.toBot g)) =
    oD l (algebraMap ℚ_[l] (Om l) ((χQ l g : ℚ_[l]ˣ) : ℚ_[l])) := by
  rw [cD_apply, Per6.χA, ACris.iota_padicInt, oD_apply, AlgHom.commutes, coe_χQ]

theorem cB_χA (g : GQ l) : Per6.cB l (Per6.χA (Per6.toBot g)) = qB l ((χQ l g : ℚ_[l]ˣ) : ℚ_[l]) :=
  ιCD_injective (((ιCD_cB _).trans (cD_χA g)).trans (ιCD_qB _).symm)

theorem tB_eq : tB l = Per6.cB l (Per6.tA l) := rfl

end GaloisCommutant

open GaloisCommutant

variable {l : ℕ} [Fact l.Prime]

theorem σB_one (b : Per6.Bcris l) : Per6.σB (1 : GQ l) b = b :=
  ιCD_injective ((ιCD_σB_aux 1 b).trans (σD_one_aux _))

theorem σB_mul (g h : GQ l) (b : Per6.Bcris l) : Per6.σB (g * h) b = Per6.σB g (Per6.σB h b) :=
  ιCD_injective (((ιCD_σB_aux (g * h) b).trans (σD_mul_aux g h _)).trans
    ((ιCD_σB_aux g _).trans (congrArg (Per6.σD g) (ιCD_σB_aux h b))).symm)

theorem ιCD_σB (g : GQ l) (b : Per6.Bcris l) : ιCD l (Per6.σB g b) = Per6.σD g (ιCD l b) :=
  ιCD_σB_aux g b

theorem σD_oD (g : GQ l) (x : Om l) : Per6.σD g (oD l x) = oD l (g x) := by
  rw [oD_apply, oD_apply, σD_algebraMap, gal_smul_algClToBdR]
  rfl

theorem φB_σB (g : GQ l) (b : Per6.Bcris l) : Per6.φB l (Per6.σB g b) = Per6.σB g (Per6.φB l b) :=
  comm_self (cB_isFrac l) _ _ (fun x =>
    (((congrArg (Per6.φB l) (σB_cB g x)).trans (φB_cB _)).trans
      (congrArg (Per6.cB l) (phi_galCris g x))).trans
      ((congrArg (Per6.σB g) (φB_cB x)).trans (σB_cB g _)).symm) b

theorem σB_tB (g : GQ l) : Per6.σB g (tB l) = qB l ((χQ l g : ℚ_[l]ˣ) : ℚ_[l]) * tB l := by
  rw [tB_eq, σB_cB, Per6.galCris_tA, map_mul, cB_χA]

end PositivityTheory.LocInh
end
end

