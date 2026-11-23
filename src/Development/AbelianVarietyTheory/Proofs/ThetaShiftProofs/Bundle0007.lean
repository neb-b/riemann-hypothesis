module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SublatticeCoefficients
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodLatticeCountable
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CountableOfIsAddFundamentalDomain

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSplitOfCoisotropicKer
section
noncomputable section

namespace GlobalTheory

namespace KerPerp

variable {O L Y : Type} [CommRing O] [StarRing O] [AddCommGroup L] [Module O L] [AddCommGroup Y] [Module O Y]
  {EF : LinearMap.BilinForm ℤ L} {y : L →ₗ[O] Y}

theorem exists_isotropic_section [Module.Projective O Y] {w : O} (hw : w + star w = 1) (halt : EF.IsAlt)
    (hb : Function.Bijective EF) (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (star a • x'))
    (hy : Function.Surjective y) (hle : ∀ t, (∀ v, y v = 0 → EF t v = 0) → y t = 0) :
    ∃ s : Y →ₗ[O] L, (∀ x, y (s x) = x) ∧ ∀ x x', EF (s x) (s x') = 0 := by
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property y LinearMap.id hy
  have hs0' : ∀ x, y (s0 x) = x := fun x => LinearMap.congr_fun hs0 x
  have skew : ∀ a b, EF a b = -EF b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add (f := _), LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
    linarith
  have hle' : kerPerp hadj y ≤ LinearMap.ker y := fun t ht => hle t (mem_kerPerp.1 ht)
  obtain ⟨be, hbe_apply⟩ : ∃ be : LinearMap.BilinForm ℤ Y,
      ∀ x x', be x x' = EF (s0 x) (s0 (w • x')) :=
    ⟨EF.compl₁₂ s0.toAddMonoidHom.toIntLinearMap
      (s0.toAddMonoidHom.toIntLinearMap ∘ₗ (LinearMap.lsmul O Y w).toAddMonoidHom.toIntLinearMap),
      fun _ _ => rfl⟩
  have hbe : ∀ (a : O) x x', be (a • x) x' = be x (star a • x') := by
    intro a x x'
    rw [hbe_apply, hbe_apply, map_smul s0 a x, hadj, map_smul s0 w (star a • x'), map_smul s0 w x',
      map_smul s0 (star a) x', smul_comm]
  have hn := neg_apply_nilTo hadj hb hy hbe
  refine ⟨s0 + (kerPerp hadj y).subtype ∘ₗ nilTo hadj hb hy hbe ∘ₗ s0, fun x => ?_, fun x x' => ?_⟩
  · have h0 : y ((nilTo hadj hb hy hbe (s0 x) : L)) = 0 :=
      LinearMap.mem_ker.1 (hle' (nilTo hadj hb hy hbe (s0 x)).2)
    simp [hs0', h0]
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add (f := _)]
    have h1 := hn (s0 x) (s0 x')
    have h2 := hn (s0 x') (s0 x)
    rw [hs0', hs0', hbe_apply] at h1 h2
    have h3 := isotropic hle' (nilTo hadj hb hy hbe (s0 x)).2 (nilTo hadj hb hy hbe (s0 x')).2
    have h4 := skew (s0 x) (nilTo hadj hb hy hbe (s0 x'))
    have k1 : EF (s0 x') (s0 (w • x)) = -EF (s0 x) (star w • s0 x') := by
      rw [map_smul s0 w x, skew, hadj]
    have k2 : EF (s0 x) (s0 x') = EF (s0 x) (s0 (w • x')) + EF (s0 x) (star w • s0 x') := by
      rw [map_smul s0 w x', ← map_add (EF (s0 x)), ← add_smul, hw, one_smul]
    linarith

end KerPerp

theorem exists_split_of_coisotropic_ker (O L Y : Type) [CommRing O] [StarRing O] [AddCommGroup L] [Module O L]
    [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] [Module.Projective O Y] (w : O)
    (EF : LinearMap.BilinForm ℤ L) (y : L →ₗ[O] Y) (hw : w + star w = 1) (halt : ∀ x, EF x x = 0)
    (hb : Function.Bijective EF) (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (star a • x'))
    (hy : Function.Surjective y) (hle : ∀ t, (∀ v, y v = 0 → EF t v = 0) → y t = 0) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module O M) (EM : LinearMap.BilinForm ℤ M) (e : L ≃+ Y × (Y →+ ℤ) × M),
      Function.Bijective EM ∧ (∀ v, (e v).1 = y v) ∧
      (∀ (a : O) v x, (e (a • v)).2.1 x = (e v).2.1 (star a • x)) ∧
      (∀ (a : O) v, (e (a • v)).2.2 = a • (e v).2.2) ∧
      ∀ v v', EF v v' = (e v').2.1 (e v).1 - (e v).2.1 (e v').1 + EM (e v).2.2 (e v').2.2 := by
  obtain ⟨s, hsy, hsiso⟩ := KerPerp.exists_isotropic_section (EF := EF) (y := y) hw halt hb hadj hy hle
  have skew : ∀ a b, EF a b = -EF b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add (f := _), LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
    linarith
  have hle' : KerPerp.kerPerp hadj y ≤ LinearMap.ker y := fun t ht =>
    hle t (KerPerp.mem_kerPerp.1 ht)
  obtain ⟨E, hE⟩ : ∃ E : KerPerp.kerPerp hadj y ≃ₗ[ℤ] Module.Dual ℤ Y,
      ∀ (t : KerPerp.kerPerp hadj y) (v : L), E t (y v) = -EF t v :=
    ⟨KerPerp.equivDual hadj hb hy, KerPerp.equivDual_apply hadj hb hy⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : L →ₗ[ℤ] Module.Dual ℤ Y, ∀ v x, Φ v x = -EF v (s x) :=
    ⟨-(EF.compl₂ s.toAddMonoidHom.toIntLinearMap), fun _ _ => rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : L →ₗ[ℤ] L, ∀ v, T v = ((E.symm (Φ v) : KerPerp.kerPerp hadj y) : L) :=
    ⟨(KerPerp.kerPerp hadj y).subtype.toAddMonoidHom.toIntLinearMap ∘ₗ E.symm.toLinearMap ∘ₗ Φ,
      fun _ => rfl⟩
  have hTK : ∀ v, T v ∈ KerPerp.kerPerp hadj y := fun v => by rw [hTdef]; exact (E.symm (Φ v)).2
  have hEF : ∀ (t : KerPerp.kerPerp hadj y) w, EF t w = -E t (y w) := fun t w => by rw [hE]; ring
  have hT : ∀ v w, EF (T v) w = EF v (s (y w)) := fun v w => by
    rw [hTdef, hEF, LinearEquiv.apply_symm_apply, hΦ, neg_neg]
  have hTy : ∀ v, y (T v) = 0 := fun v => LinearMap.mem_ker.1 (hle' (hTK v))
  obtain ⟨P, hP⟩ : ∃ P : L →ₗ[ℤ] L, ∀ v, P v = v - s (y v) - T v :=
    ⟨LinearMap.id - s.toAddMonoidHom.toIntLinearMap ∘ₗ y.toAddMonoidHom.toIntLinearMap - T,
      fun _ => rfl⟩
  have hPy : ∀ v, y (P v) = 0 := fun v => by
    rw [hP, map_sub, map_sub, hsy, hTy, sub_self, sub_zero]
  have hPs : ∀ v x, EF (P v) (s x) = 0 := fun v x => by
    rw [hP]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hsiso, hT, hsy]
    ring
  obtain ⟨N, hN⟩ : ∃ N : Submodule O L, ∀ v, v ∈ N ↔ y v = 0 ∧ ∀ x, EF v (s x) = 0 :=
    ⟨{ carrier := {v | y v = 0 ∧ ∀ x, EF v (s x) = 0}
       add_mem' := fun {a b} ha hb => ⟨by rw [map_add (f := _), ha.1, hb.1, add_zero],
         fun x => by rw [map_add (f := _), LinearMap.add_apply, ha.2, hb.2, add_zero]⟩
       zero_mem' := ⟨map_zero y, fun x => by rw [map_zero, LinearMap.zero_apply]⟩
       smul_mem' := fun c v hv => ⟨by rw [map_smul, hv.1, smul_zero],
         fun x => by rw [hadj, ← map_smul s, hv.2]⟩ }, fun _ => Iff.rfl⟩
  have hPN : ∀ v, P v ∈ N := fun v => (hN _).2 ⟨hPy v, hPs v⟩
  have hΦN : ∀ m ∈ N, Φ m = 0 := fun m hm => LinearMap.ext fun x => by
    rw [hΦ, ((hN m).1 hm).2, neg_zero, LinearMap.zero_apply]
  have hPfix : ∀ m ∈ N, P m = m := fun m hm => by
    simp [hP, ((hN m).1 hm).1, hTdef, hΦN m hm]
  have hTsmul : ∀ (a : O) v, T (a • v) = a • T v := fun a v => hb.1 (LinearMap.ext fun w => by
    rw [hT, hadj, hadj, hT, map_smul y, map_smul s])
  have hdec : ∀ v, v = s (y v) + T v + P v := fun v => by rw [hP]; abel
  have hback : ∀ φ : Module.Dual ℤ Y, φ.toAddMonoidHom.toIntLinearMap = φ :=
    fun φ => LinearMap.ext fun _ => rfl
  let e : L ≃+ Y × (Y →+ ℤ) × N :=
    { toFun := fun v => (y v, (Φ v).toAddMonoidHom, ⟨P v, hPN v⟩)
      invFun := fun p => s p.1 + ((E.symm p.2.1.toIntLinearMap : KerPerp.kerPerp hadj y) : L) +
        (p.2.2 : L)
      left_inv := fun v => by
        show s (y v) + ((E.symm (Φ v).toAddMonoidHom.toIntLinearMap : KerPerp.kerPerp hadj y) : L) +
          P v = v
        rw [hback, ← hTdef]
        exact (hdec v).symm
      right_inv := fun p => by
        obtain ⟨a, φ, m⟩ := p
        have hyt : y ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) = 0 :=
          LinearMap.mem_ker.1 (hle' (E.symm _).2)
        have hym : y (m : L) = 0 := ((hN m).1 m.2).1
        have hyv : y (s a + ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) + m) = a := by
          rw [map_add (f := _), map_add (f := _), hsy, hyt, hym, add_zero, add_zero]
        have hΦv : Φ (s a + ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) + m) =
            φ.toIntLinearMap := by
          refine LinearMap.ext fun x => ?_
          rw [hΦ, map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hsiso, hEF, hsy,
            LinearEquiv.apply_symm_apply, ((hN m).1 m.2).2]
          simp
        refine Prod.ext hyv (Prod.ext (AddMonoidHom.ext fun x => ?_) (Subtype.ext ?_))
        · show Φ _ x = φ x
          rw [hΦv]
          rfl
        · show P _ = m
          rw [hP, hyv, hTdef, hΦv]
          exact (fun p q r : L => show p + q + r - p - q = r by abel) _ _ _
      map_add' := fun a b => by
        refine Prod.ext (map_add y a b) (Prod.ext (AddMonoidHom.ext fun x => ?_) (Subtype.ext ?_))
        · show Φ (a + b) x = Φ a x + Φ b x
          rw [map_add (f := _), LinearMap.add_apply]
        · show P (a + b) = P a + P b
          exact map_add P a b }
  refine ⟨N, inferInstance, inferInstance,
    EF.compl₁₂ N.subtype.toAddMonoidHom.toIntLinearMap N.subtype.toAddMonoidHom.toIntLinearMap, e,
    ⟨?_, ?_⟩, fun v => rfl, ?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    apply Subtype.ext
    apply hb.1
    refine LinearMap.ext fun w => ?_
    have hm' : EF (m : L) (P w) = 0 := by
      simpa using LinearMap.congr_fun hm ⟨P w, hPN w⟩
    have hmN := (hN m).1 m.2
    rw [Submodule.coe_zero, map_zero, LinearMap.zero_apply, hdec w, map_add (f := _), map_add (f := _), hmN.2, hm',
      skew, hT, hmN.1, map_zero, map_zero]
    simp
  · intro g
    obtain ⟨v, hv⟩ := hb.2 (g ∘ₗ (AddMonoidHom.mk' (fun v => (⟨P v, hPN v⟩ : N))
      (fun a b => Subtype.ext (map_add P a b))).toIntLinearMap)
    refine ⟨⟨P v, hPN v⟩, LinearMap.ext fun m => ?_⟩
    have h1 : EF v m = g ⟨P m, hPN m⟩ := LinearMap.congr_fun hv m
    have h2 : (⟨P m, hPN m⟩ : N) = m := Subtype.ext (hPfix m m.2)
    have hmN := (hN m).1 m.2
    show EF (P v) m = g m
    rw [hP]
    simp only [map_sub, LinearMap.sub_apply]
    rw [h1, h2, skew (s (y v)), hmN.2, hT, hmN.1, map_zero, map_zero]
    simp
  · intro a v x
    show Φ (a • v) x = Φ v (star a • x)
    rw [hΦ, hΦ, hadj, map_smul s]
  · intro a v
    refine Subtype.ext ?_
    show P (a • v) = a • P v
    rw [hP, hP, map_smul y, map_smul s, hTsmul, smul_sub, smul_sub]
  · intro v v'
    show EF v v' = Φ v' (y v) - Φ v (y v') + EF (P v) (P v')
    rw [hΦ, hΦ, hP, hP]
    simp only [map_sub, LinearMap.sub_apply]
    have f1 := hT v v'
    have f2 := hT v (s (y v'))
    rw [hsy] at f2
    have f3 : EF v (T v') = -EF v' (s (y v)) := by rw [skew, hT]
    have f4 : EF (s (y v)) (T v') = -EF v' (s (y (s (y v)))) := by rw [skew, hT]
    rw [hsy] at f4
    have f5 := hsiso (y v) (y v')
    have f6 : EF (T v) (T v') = 0 := KerPerp.isotropic hle' (hTK v) (hTK v')
    have f7 := skew (s (y v)) v'
    linarith

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermitianMatrixRealizesCuspCoords
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate

namespace GlobalTheory.HermExpo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem sum_re_eq_trace (X : Data E r) (x : E) :
    ∑ τ : X.Ψ, (τ.1 (x + cc x)).re = ((Algebra.trace ℚ E x : ℚ) : ℝ) := by
  first
  | exact @_root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj
  | exact _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj
  | (apply _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj ..)

theorem kappa_ne (X : Data E r) : X.κ0 ≠ 0 := by
  have := X.ξ0_ne
  rcases X.κ0_xi with h | h <;> rw [h] <;> simpa using this

theorem exists_trace_repr (f : Matrix (Fin ρ) (Fin ρ) E →ₗ[ℚ] ℚ) :
    ∃ c : Matrix (Fin ρ) (Fin ρ) E, ∀ β,
      f β = Algebra.trace ℚ E (∑ a, ∑ b, c a b * β a b) := by
  have h : ∀ g : E →ₗ[ℚ] ℚ, ∃ c : E, ∀ y, g y = Algebra.trace ℚ E (c * y) := by
    intro g
    refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm g, fun y => ?_⟩
    rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  choose c hc using fun a b : Fin ρ => h (f ∘ₗ Matrix.singleLinearMap ℚ a b)
  refine ⟨Matrix.of c, fun β => ?_⟩
  conv_lhs => rw [Matrix.matrix_eq_sum_single β]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Matrix.of_apply, ← hc]
  rfl

theorem exists_herm_phase (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ)
    (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (m : Fin (nZ X ρ) → ℤ) :
    ∃ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ ∧ ∀ k, phZ X cu χ k = m k := by
  have hli : LinearIndependent ℚ (zBas X cu) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.1
  obtain ⟨f, hf⟩ : ∃ f : Matrix (Fin ρ) (Fin ρ) E →ₗ[ℚ] ℚ, ∀ k, f (zBas X cu k) = m k := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
      (Finsupp.linearCombination ℚ (zBas X cu)) (LinearMap.ker_eq_bot.2 hli)
    refine ⟨Finsupp.linearCombination ℚ (fun k => (m k : ℚ)) ∘ₗ g, fun k => ?_⟩
    have h1 := LinearMap.congr_fun hg (Finsupp.single k 1)
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
      LinearMap.id_apply] at h1
    simp [h1]
  obtain ⟨c, hc⟩ := exists_trace_repr f
  have hκ : X.κ0 / 2 ≠ 0 := div_ne_zero (kappa_ne X) two_ne_zero
  have hκc : cc (X.κ0 / 2) = -(X.κ0 / 2) := by
    have := maxCuspsA_kappa_cc X
    unfold cc at this ⊢
    rw [map_div₀, this, map_ofNat, neg_div]
  have hcc : ∀ y : E, cc (cc y) = y := fun y => IsCMField.complexConj_apply_apply E y
  have hmul : ∀ y z : E, cc (y * z) = cc y * cc z := fun y z => map_mul _ y z
  have hadd : ∀ y z : E, cc (y + z) = cc y + cc z := fun y z => map_add _ y z
  have hsub : ∀ y z : E, cc (y - z) = cc y - cc z := fun y z => map_sub _ y z
  refine ⟨Matrix.of fun a b => (X.κ0 / 2) * (c a b - cc (c b a)), fun a b => ?_, fun k => ?_⟩
  · simp only [Matrix.of_apply, hmul, hsub, hκc, hcc]
    ring
  · have hs := zBas_skew X cu ⟨_, hb⟩ k
    have hx : Matrix.trace ((Matrix.of fun a b => (X.κ0 / 2) * (c a b - cc (c b a))).transpose *
        zBas X cu k) / (X.κ0 / 2) =
        (∑ a, ∑ b, c a b * zBas X cu k a b) + cc (∑ a, ∑ b, c a b * zBas X cu k a b) := by
      have h1 : cc (∑ a, ∑ b, c a b * zBas X cu k a b) =
          ∑ a, ∑ b, -(cc (c b a) * zBas X cu k a b) := by
        rw [Finset.sum_comm]
        unfold cc
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [show IsCMField.complexConj E (zBas X cu k b a) = cc (zBas X cu k b a) from rfl, hs,
          mul_neg]
      rw [h1, div_eq_iff hκ, ← Finset.sum_add_distrib]
      simp only [← Finset.sum_add_distrib, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    unfold phZ prE
    rw [hx, sum_re_eq_trace, ← hc, hf]
    simp

end GlobalTheory.HermExpo

theorem GlobalTheory.exists_isHermE_phZ_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ m : Fin (nZ X ρ) → ℤ, ∃ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ ∧ ∀ k, phZ X cu χ k = m k :=
  GlobalTheory.HermExpo.exists_herm_phase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspKilledCoefficientEqZero
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

namespace GlobalTheory.MaxCuspKilled

open MeasureTheory GlobalTheory.TorusFourier

noncomputable def dotForm {ι : Type} [Fintype ι] (c : ℝ) (v : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun t := c * ∑ k, v k * t k
  map_add' s t := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a s := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem dotForm_apply {ι : Type} [Fintype ι] (c : ℝ) (v t : ι → ℝ) :
    dotForm c v t = c * ∑ k, v k * t k := rfl

theorem coefFn_eq_cubeCoeff {Ω : Type} {N : ℕ} (act : (Fin N → ℝ) → Ω → Ω) (ph : Fin N → ℝ)
    (P : Ω → ℂ) (x : Ω) :
    coefFn act ph P x =
      cubeCoeff (Pi.basisFun ℝ (Fin N)) (fun t => P (act t x)) (dotForm 1 ph) := by
  have h : ∀ t : Fin N → ℝ, ∑ i, t i • Pi.basisFun ℝ (Fin N) i = t := fun t =>
    (Pi.basisFun ℝ (Fin N)).sum_repr t
  unfold coefFn cubeCoeff cube
  rw [← Set.pi_univ_Icc]
  simp only [h]
  congr 1
  funext t
  have hphase : (∑ k, t k * ph k) = ∑ k, ph k * t k :=
    Finset.sum_congr rfl fun k _ => mul_comm (t k) (ph k)
  simp only [integrand, chr, eNeg, dotForm_apply, one_mul, hphase]

theorem herm_comb {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ} {X : Data E r}
    (cu : CuspFD X ρ) (η : Fin ρ → E) :
    herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) = 0 := by
  have key : herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) =
      ∑ a, ∑ b, η a * cc (η b) * herm X.Gm (cu.e a) (cu.e b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, cc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      Finset.mul_sum, Finset.sum_mul]
    calc _ = ∑ k, ∑ b, ∑ l, ∑ a, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ b, ∑ k, ∑ a, ∑ l, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ b, ∑ a, ∑ k, ∑ l, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l)) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
  rw [key]
  simp [cu.iso]

theorem coefFn_eq_zero_of_killed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), (∀ cu : CuspFD X ρ, ∃ bs, IsZBasis X cu bs) → ∀ (la : Wt X.Ψ r), (∀ (cu : CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), β ∈ zGam X cu → ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1) → ∀ (c : ℝ) (P : Frame X.Ψ r → ℂ), P ∈ X.SSgt la c → ∀ (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsExpoFD X cu χ → KilledFD X cu χ c → ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0 := by
  intro E _ _ _ r ρ X hbas la hchi c P hP cu χ hχ hK x hx
  obtain ⟨η, hη0, hηΛ, hηc⟩ := hK
  have hb : IsZBasis X cu (zBas X cu) := Classical.epsilon_spec (hbas cu)
  have hsec : X.IsSec la P := hP.1.1.1
  have hdom : ∀ u, zAct X cu u x ∈ X.dom := fun u =>
    zAct_mem_dom X cu (zBas_skew X cu (hbas cu)) u x hx
  obtain ⟨L, hL1, hL2, hL3⟩ := _root_.GlobalTheory.CuspFlow.flow_eq_zAct E r ρ X cu hb η hηΛ
  have hiso : X.IsIso (∑ a, η a • cu.e a) :=
    ⟨hηΛ, herm_comb cu η, fun h => hη0 (funext (Fintype.linearIndependent_iff.1 cu.ind η h))⟩
  set ν : X.Ψ → ℝ := fun τ => (τ.1 (hq χ η)).re with hν
  set g : (Fin (nZ X ρ) → ℝ) → ℂ := fun t => P (zAct X cu t x) with hg
  have hgc : Continuous g := hsec.1.continuousOn.comp_continuous (continuous_zAct X cu x) hdom
  have hper : ∀ l : Fin (nZ X ρ) → ℝ, (∀ k, ∃ z : ℤ, l k = z) → ∀ u, g (u + l) = g u := by
    intro l hl u
    choose n hn using hl
    have : l = fun i => (n i : ℝ) := funext hn
    rw [this]
    exact maxCuspsA_periodic X cu hb la (hchi cu) P hsec x hx u n
  have hcomp : dotForm 1 (phZ X cu χ) ∘ₗ L = dotForm 2 ν := by
    refine LinearMap.ext fun s => ?_
    rw [LinearMap.comp_apply, dotForm_apply, dotForm_apply, one_mul, hL2 χ hχ.1 s]
  have hfreq : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k := by
    intro p hp
    choose n hn using hL3 la p hp
    choose m hm using hχ.2
    refine ⟨∑ k, m k * n k, ?_⟩
    rw [← hL2 χ hχ.1 p]
    simp only [hn, hm]
    push_cast
    rfl
  have hex := PeriodLatticeCountable.fd_exists X la
  obtain ⟨-, hD, h0, h1⟩ := hex.choose_spec
  obtain ⟨H₁, -, -⟩ := partialCoeff_spec_cube (Pi.basisFun ℝ (Fin (nZ X ρ))) hD h0.ne' h1.ne L hgc
    (fun i => hper _ fun k => ⟨if k = i then 1 else 0, by
      by_cases h : k = i <;> simp [h]⟩)
    (fun l hl => hper _ (hL3 la l hl))
  obtain ⟨-, -, -, B⟩ := H₁ (dotForm 2 ν) hfreq
  rw [coefFn_eq_cubeCoeff]
  refine B.1 ?_ _ (fun i => ?_) hcomp
  · funext b
    have h := hP.2 _ hiso ν hηc _ (hdom b)
    rw [Data.fj, if_pos hfreq, dite_eq_left hex] at h
    rw [partialCoeff, coeff_eq, Pi.zero_apply, ← h]
    congr 2
    funext s
    rw [hL1, maxCuspsA_zAct_add, add_comm (L s), dotForm_apply]
    congr 2
    push_cast
    ring
  · obtain ⟨z, hz⟩ := hχ.2 i
    exact ⟨z, by simp [dotForm_apply, Pi.single_apply, hz]⟩

end GlobalTheory.MaxCuspKilled
end

