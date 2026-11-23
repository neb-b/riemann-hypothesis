module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCoprimeOfCongrMulOneSubModLevel
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusCop

theorem natCoprime_of_zmod_mul_one_sub : ∀ (I : AutInst) (g T M : ℕ), 1 ≤ g → Nat.Coprime M g →
    ZMod' I g ((M : I.E ⊗[I.F] Af I.F) * (1 - (T : I.E ⊗[I.F] Af I.F))) → Nat.Coprime T g := by
  intro I g T M hg hMg hz
  obtain ⟨t, ht, hc⟩ := hz
  obtain ⟨-, hint, hu, -⟩ := GlobalTheory.RowLev.intAf_approx_inter_unit_conj I g hg
  have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  set q : ℚ := (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) / (g : ℚ) with hqdef
  have hgq : (g : I.E) * (q : I.E) = (M : I.E) * (1 - (T : I.E)) := by
    have : (g : ℚ) * q = (M : ℚ) * (1 - (T : ℚ)) := by
      rw [hqdef]; field_simp; push_cast; ring
    have := congrArg (fun x : ℚ => (x : I.E)) this
    simpa using this
  have key : Formalism.UG.inclE (F := I.F) (Af I.F) (q : I.E) = t := by
    apply hu.mul_left_cancel
    rw [← hc]
    calc (g : I.E ⊗[I.F] Af I.F) * Formalism.UG.inclE (F := I.F) (Af I.F) (q : I.E)
        = Formalism.UG.inclE (F := I.F) (Af I.F) ((g : I.E) * (q : I.E)) := by rw [map_mul, map_natCast]
      _ = Formalism.UG.inclE (F := I.F) (Af I.F) ((M : I.E) * (1 - (T : I.E))) := by rw [hgq]
      _ = _ := by rw [map_mul, map_sub, map_one, map_natCast, map_natCast]
  have hq : (q : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := (hint _).1 (key ▸ ht)
  obtain ⟨b, hb⟩ := hq
  have h1 : IsIntegral ℤ (algebraMap ℚ I.E q) := by
    rw [eq_ratCast, ← hb]; exact RingOfIntegers.isIntegral_coe b
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff ).1 h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have h3 : (M : ℤ) * (1 - (T : ℤ)) = (g : ℤ) * n := by
    have hn' : (n : ℚ) = q := by simpa using hn
    have : (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) = (((g : ℤ) * n : ℤ) : ℚ) := by
      rw [hqdef] at hn'
      push_cast
      rw [hn']
      field_simp
      push_cast; ring
    exact_mod_cast this
  have h5 : (g : ℤ) ∣ 1 - (T : ℤ) := by
    refine Int.dvd_of_dvd_mul_right_of_gcd_one ⟨n, h3⟩ ?_
    rw [Int.gcd_natCast_natCast]; exact hMg.symm
  have hd1 : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1 := by
    have a : ((Nat.gcd T g : ℕ) : ℤ) ∣ (T : ℤ) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)
    have b : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1 - (T : ℤ) :=
      (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).trans h5
    have := dvd_add b a
    simpa using this
  exact Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 (by simpa using hd1))

end GlobalTheory.TorusCop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SetCut

variable {D : D7}

def indQ (D : D7) (Q : Finset (Pl D)) : Af D.host.F := ∑ v ∈ Q, singleV D.host.F v 1

def idemQ (D : D7) (Q : Finset (Pl D)) : AF D.host.F := pairA D.host.F 0 (indQ D Q)

def idemQc (D : D7) (Q : Finset (Pl D)) : AF D.host.F := pairA D.host.F 0 (1 - indQ D Q)

open Classical in
theorem evalV_indQ (Q : Finset (Pl D)) (w : Pl D) :
    evalV D.host.F w (indQ D Q) = if w ∈ Q then 1 else 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [indQ, map_sum]
  have h : ∀ v ∈ Q, evalV D.host.F w (singleV D.host.F v 1) = if w = v then 1 else 0 := by
    intro v _
    by_cases hwv : w = v
    · subst hwv
      rw [if_pos rfl]
      change (singleV D.host.F w 1) w = 1
      exact RestrictedProduct.single_eq_same _ _ _
    · rw [if_neg hwv]
      change (singleV D.host.F v 1) w = 0
      exact RestrictedProduct.single_eq_of_ne (fun u : Pl D => u.adicCompletionIntegers D.host.F)
        (1 : Fv D.host.F v) hwv
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]

theorem parts_pairA (α : Af D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
        evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have ha : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨?_, fun w => ?_⟩
  · rw [ha]
    change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  · exact (placeIdempotent_infinite_and_finite_components D w _ α rfl).2 w

open Classical in
theorem parts_idemQ (Q : Finset (Pl D)) :
    infPart D (algebraMap (AF D.host.F) (AE D) (idemQ D Q)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (idemQ D Q)) = if w ∈ Q then 1 else 0 := by
  refine ⟨(parts_pairA _).1, fun w => ?_⟩
  rw [idemQ, (parts_pairA _).2 w, evalV_indQ]
  split_ifs
  · rfl
  · exact TensorProduct.zero_tmul _ _

open Classical in
theorem parts_idemQc (Q : Finset (Pl D)) :
    infPart D (algebraMap (AF D.host.F) (AE D) (idemQc D Q)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (idemQc D Q)) = if w ∈ Q then 0 else 1 := by
  refine ⟨(parts_pairA _).1, fun w => ?_⟩
  rw [idemQc, (parts_pairA _).2 w, map_sub, map_one, evalV_indQ]
  split_ifs
  · rw [sub_self]; exact TensorProduct.zero_tmul _ _
  · rw [sub_zero]; rfl

theorem mem_idAt_iff_mul (P : Pl D → Prop) [DecidablePred P] (c : AE D) (h0 : infPart D c = 0)
    (hc : ∀ w, compAt D w c = if P w then 1 else 0) (a : AE D) : a ∈ idAt D P ↔ c * a = a := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
  constructor
  · rintro ⟨ha0, haw⟩
    rw [← sub_eq_zero]
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_sub, RingHom.map_mul, h0, ha0, zero_mul, sub_zero]
    · intro w
      rw [RingHom.map_sub, RingHom.map_mul, hc w]
      by_cases h : P w
      · rw [if_pos h, one_mul, sub_self]
      · rw [if_neg h, haw w h, zero_mul, sub_zero]
  · intro ha
    refine ⟨?_, fun w hw => ?_⟩
    · rw [← ha, RingHom.map_mul, h0, zero_mul]
    · rw [← ha, RingHom.map_mul, hc w, if_neg hw, zero_mul]

theorem mem_idOff_iff_mul (P : Pl D → Prop) [DecidablePred P] (c : AE D) (h0 : infPart D c = 0)
    (hc : ∀ w, compAt D w c = if P w then 1 else 0) (a : AE D) : a ∈ idOff D P ↔ c * a = 0 := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  constructor
  · intro ha
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_mul, h0, zero_mul]
    · intro w
      rw [RingHom.map_mul, hc w]
      by_cases h : P w
      · rw [ha w h, mul_zero]
      · rw [if_neg h, zero_mul]
  · intro ha w hw
    have := congrArg (compAt D w) ha
    rwa [RingHom.map_mul, hc w, if_pos hw, one_mul, RingHom.map_zero] at this

open Classical in
theorem mem_idAt_Q_iff (Q : Finset (Pl D)) (a : AE D) :
    a ∈ idAt D (· ∈ Q) ↔ algebraMap (AF D.host.F) (AE D) (idemQ D Q) * a = a :=
  mem_idAt_iff_mul (· ∈ Q) _ (parts_idemQ Q).1 (parts_idemQ Q).2 a

open Classical in
theorem mem_idAt_Qc_iff (Q : Finset (Pl D)) (a : AE D) :
    a ∈ idAt D (· ∉ Q) ↔ algebraMap (AF D.host.F) (AE D) (idemQc D Q) * a = a :=
  mem_idAt_iff_mul (· ∉ Q) _ (parts_idemQc Q).1
    (fun w => by rw [(parts_idemQc Q).2 w]; by_cases h : w ∈ Q <;> simp [h]) a

theorem idemQ_mul_self (Q : Finset (Pl D)) : idemQ D Q * idemQ D Q = idemQ D Q := by
  have e : (idemQ D Q * idemQ D Q : AF D.host.F) = pairA D.host.F 0 (indQ D Q * indQ D Q) :=
    Prod.ext (mul_zero _) rfl
  rw [e, idemQ]
  congr 1
  apply RestrictedProduct.ext
  intro w
  have h := evalV_indQ (D := D) Q w
  change evalV D.host.F w (indQ D Q * indQ D Q) = evalV D.host.F w (indQ D Q)
  rw [map_mul, h]
  split_ifs <;> simp

theorem one_sub_idemQ_mul_self (Q : Finset (Pl D)) :
    (1 - idemQ D Q) * (1 - idemQ D Q) = 1 - idemQ D Q := by
  have h := idemQ_mul_self (D := D) Q
  linear_combination h

theorem mem_congGrp_iff (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  change ((matHom V g).1.map (Ideal.Quotient.mk I)) i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j ↔ _
  rw [Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, map_one]
    rfl
  · simp only [Matrix.one_apply_ne hij, map_zero]
    rfl

def cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) : GA D V →* GA D V :=
  GlobalTheory.UnitaryIdemCut.cutUJ (sigR (AF D.host.F) D.sp.cm.sig) (JR (AF D.host.F) V.gram)
    (algebraMap (AF D.host.F) (AE D) ε) (by rw [← map_mul, hε])
    (GlobalTheory.UnitaryIdemCut.sigR_algebraMap (AF D.host.F) D.sp.cm.sig ε)

theorem mt_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) (g : GA D V) :
    Formalism.L2.Theta.mt V (cutG V ε hε g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt V g +
      (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

end GlobalTheory.FinPl.SetCut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrderedProdLocalPartsSeparatesPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.SepProd

variable {D : D7}

theorem list_ofFn_prod_eq {M : Type*} [Monoid M] : ∀ {n : ℕ} (f : Fin n → M) (i : Fin n), (∀ j, j ≠ i → f j = 1) →
    (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | n + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · have hprod : (List.ofFn fun j : Fin n => f j.succ).prod = 1 :=
        List.prod_eq_one (List.forall_mem_ofFn_iff.mpr fun j => h _ (Fin.succ_ne_zero j))
      rw [hprod, mul_one]
    · rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact list_ofFn_prod_eq (fun j => f j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

theorem mem_grpOff_of_suppAt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) {V : HSp D} {g : GA D V} (hg : SuppAt p.e V g) {v : GlobalTheory.FinPl.Pl D} (hv : p.v ≠ v) :
    g ∈ grpOff V (· = v) := by
  rw [grpOff, congGrp, MonoidHom.mem_ker]
  ext i j
  change Ideal.Quotient.mk _ (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
  rw [← Matrix.map_one (Ideal.Quotient.mk (idOff D (· = v))) (map_zero _) (map_one _), Matrix.map_apply,
    Ideal.Quotient.eq]
  have hmem : Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ idAt D (· = p.v) := by
    have := hg i j
    rw [Matrix.sub_apply] at this
    rw [← this]
    exact Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.FrameLat.sum_mem_idAt p)
  have h2 := (Ideal.mem_inf.1 hmem).2
  rw [Ideal.mem_iInf] at h2
  rw [idOff, Ideal.mem_iInf]
  rintro ⟨w, rfl⟩
  exact h2 ⟨w, fun e => hv e.symm⟩

end GlobalTheory.SeeSaw.SepProd


open GlobalTheory.SeeSaw.SepProd in
theorem GlobalTheory.SeeSaw.SepProd.prod_sep : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ) (xs : Fin n → GA D (c.V j')), (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) → ∀ (i : Fin n), ∃ y ∈ grpOff (c.V j') (· = (G i).q.v), (List.ofFn xs).prod = xs i * y := by
  intro D c v n G hG j' xs hxs i
  refine ⟨(xs i)⁻¹ * (List.ofFn xs).prod, ?_, by rw [mul_inv_cancel_left]⟩
  have hoff : ∀ i', i' ≠ i → xs i' ∈ grpOff (c.V j') (· = (G i).q.v) := fun i' hi' =>
    mem_grpOff_of_suppAt (G i').q (hxs i') fun e => hi' (hG.inj e)
  rw [grpOff, congGrp, MonoidHom.mem_ker, map_mul, map_inv, map_list_prod, List.map_ofFn,
    list_ofFn_prod_eq (_ ∘ xs) i fun j hj => MonoidHom.mem_ker.1 (hoff j hj), Function.comp_apply, inv_mul_cancel]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanFixesBasisAndIdemp
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ScalW

open Formalism.L2.SG.PoincareInHH.Cut

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hA_eV_eV (a b : Fin D.R.rS) : hA X.B.I (eV X a) (eV X b) = 0 := by
  rw [eV, eV, HidaSetting.eR, HidaSetting.eR, hA_crd, X.ee]
  simp

theorem hA_fV_fV (a b : Fin D.R.rS) : hA X.B.I (fV X a) (fV X b) = 0 := by
  rw [fV, fV, HidaSetting.fR, HidaSetting.fR, hA_crd, X.ff]
  simp

theorem hA_eV_fV (a b : Fin D.R.rS) : hA X.B.I (eV X a) (fV X b) = if a = b then 1 else 0 := by
  rw [eV, fV, HidaSetting.eR, HidaSetting.fR, hA_crd, X.ef]
  split_ifs <;> simp

theorem hA_fV_eV (a b : Fin D.R.rS) : hA X.B.I (fV X a) (eV X b) = if b = a then 1 else 0 :=
  hA_f_e X a b

theorem hA_zV_eV (a : Fin D.R.rS) : hA X.B.I (zV X u) (eV X a) = 0 := by
  have h := (VS D).herm.eq (X.eX a) (X.zu u)
  rw [(X.zu_orth u a).1, map_zero] at h
  rw [zV, eV, HidaSetting.zR, HidaSetting.eR, hA_crd, ← h]
  simp

theorem hA_zV_fV (a : Fin D.R.rS) : hA X.B.I (zV X u) (fV X a) = 0 := by
  have h := (VS D).herm.eq (X.fY a) (X.zu u)
  rw [(X.zu_orth u a).2, map_zero] at h
  rw [zV, fV, HidaSetting.zR, HidaSetting.fR, hA_crd, ← h]
  simp

theorem hA_eV_zV (a : Fin D.R.rS) : hA X.B.I (eV X a) (zV X u) = 0 := by
  rw [zV, eV, HidaSetting.zR, HidaSetting.eR, hA_crd, (X.zu_orth u a).1]
  simp

theorem hA_fV_zV (a : Fin D.R.rS) : hA X.B.I (fV X a) (zV X u) = 0 := adelicHermitian_hyperbolicF_anisotropic_eq_zero X u a

theorem hA_zV_zV : hA X.B.I (zV X u) (zV X u) =
    -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
  rw [zV, HidaSetting.zR, hA_crd, X.zu_norm]
  simp

theorem divN_zero' : divN X.B.I (D.mem u).A.T 0 = 0 := by
  simp [divN]

theorem prj_eV (b : Fin D.R.rS) : prj X u (eV X b) = eV X b := by
  simp only [prj, hA_fV_eV, hA_eV_eV, hA_zV_eV, divN_zero', ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero, sub_zero]

theorem prj_fV (b : Fin D.R.rS) : prj X u (fV X b) = fV X b := by
  simp only [prj, hA_fV_fV, hA_eV_fV, hA_zV_fV, divN_zero', ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, zero_add, sub_zero]

theorem prj_zV : prj X u (zV X u) = zV X u := by
  have hT : ((D.mem u).A.T : ℕ) ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have h : divN X.B.I (D.mem u).A.T (-(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) = -1 := by
    rw [show -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (-1) by ring]
    exact Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul X.B.I _ hT _
  simp only [prj, hA_fV_zV, hA_eV_zV, hA_zV_zV, h, zero_smul, Finset.sum_const_zero, zero_add,
    neg_smul, one_smul, sub_neg_eq_add]

theorem prj_prj (y : VA X.B.I) : prj X u (prj X u y) = prj X u y := by
  have hL : ∀ z, prjL X u z = prj X u z := fun _ => rfl
  rw [← hL (prj X u y)]
  conv_lhs => arg 2; rw [prj]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_add (f := _), map_sum, map_smul]
  simp only [hL, prj_eV, prj_fV, prj_zV]
  rfl

theorem prj_fix_idem : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧
      GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) ∧
    GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u ∧
    ∀ y, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.prj X u y) = GlobalTheory.ScalW.prj X u y :=
  fun _ X u => ⟨fun a => ⟨prj_eV X u a, prj_fV X u a⟩, prj_zV X u, prj_prj X u⟩

end GlobalTheory.ScalW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthProjHyperbolicNegativeSpanSelfAdjoint
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalW


open Formalism.L2.SG.Pf.unitaryCongruence in
theorem prj_selfAdjoint : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (x y : VA X.B.I),
    hA X.B.I (GlobalTheory.ScalW.prj X u x) y = hA X.B.I x (GlobalTheory.ScalW.prj X u y) := by
  intro D X u x y
  have hT : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have hsum : ∀ (w : VA X.B.I) (g : Fin D.R.rS → VA X.B.I), hA X.B.I w (∑ a, g a) = ∑ a, hA X.B.I w (g a) :=
    fun w g => map_sum (hL X.B.I w) g Finset.univ
  have hd : ∀ c, divN X.B.I (D.mem u).A.T c = divN X.B.I (D.mem u).A.T 1 * c := by
    intro c; unfold divN; ring
  have hs : sigA X.B.I (divN X.B.I (D.mem u).A.T 1) = divN X.B.I (D.mem u).A.T 1 := by
    have h2 := congrArg (sigA X.B.I) (gmul_divN X.B.I _ hT 1)
    rw [map_mul, map_natCast, map_one] at h2
    rw [← divN_gmul X.B.I _ hT (sigA X.B.I _), h2]
  rw [hA_symm X.B.I y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [prj, hA_sub_right, hA_add_right, hA_smul_right, hsum, map_sub, map_add (f := _), map_sum, map_mul]
  rw [hd (hA X.B.I (zV X u) x), hd (hA X.B.I (zV X u) y), map_mul, hs]
  simp only [← hA_symm]
  rw [add_comm (∑ a, _ * hA X.B.I x (eV X a))]
  simp only [mul_comm (hA X.B.I x _)]
  ring

end GlobalTheory.ScalW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RatMulVecSec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreFrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem rat_mulVec_sec (q : SplitPt D k) {a b : ℕ} (Q : Matrix (Fin a) (Fin b) D.host.E) (w : Fin b → k) :
    rat Q *ᵥ (fun i => q.sec (w i)) =
      fun i => q.sec ((Q.map (GlobalTheory.SliceModel.prH (GlobalTheory.LocMod.ofSplit q)) *ᵥ w) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.SliceModel.ι_mul_left (GlobalTheory.LocMod.ofSplit q) (w j) (incA D (Q i j))

end GlobalTheory.CoreFrameLat
end
end

