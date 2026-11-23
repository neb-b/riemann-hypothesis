module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitIdemDict

open GlobalTheory.AdelicU

variable {D : D7} {v : FinPl D}

theorem exists_eq_splitProj (φ : SplitProj D v) :
    ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, φ = splitProj τ := by
  refine ⟨(φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight, ?_⟩
  refine AlgHom.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>

    have hax : a ⊗ₜ[D.host.F] x = a • ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [splitProj_tmul, hax, map_smul, smul_eq_mul]
    rfl
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]

theorem isProjAt_iff (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (PP : Formalism.L2.DIV.Pl D.host.E) :
    IsProjAt (D := D) (v := v) (splitProj τ) PP ↔ PP = splitPrime τ := by

  have hred : ∀ x : 𝓞 D.host.E, rdQ (D := D) (v := v) (splitProj τ) (x : D.host.E) = τ x := fun x => by
    simp only [rdQ, splitProj_tmul, one_mul]
  unfold IsProjAt
  constructor
  · intro h
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    rw [h x, hred, mem_splitPrime]
  · rintro rfl x
    rw [hred, mem_splitPrime]

theorem sigR_compFin {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    sigR _ σ (compFin F E v z) = compFin F E v (sigR _ σ z) := by

  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => simp [sigR, compFin]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem compFin_cA (z : AE D) :
    sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) = compFin D.host.F D.host.E v (cA D z) := by

  have h := sigR_compFin D.sp.cm.sig v z
  exact h

private theorem idem_inl_eq_tensAt_one (D : D7) (v : FinPl D) :
    GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl v) = GlobalTheory.EmbChart.tensAt D.host.E v 1 := by
  rw [Algebra.TensorProduct.one_def, GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem eq_idem {τ : D.host.E →ₐ[D.host.F] Fv D.host.F v} {e : AE D} (he : IsIdemOf (D := D) (v := v) (splitProj τ) e) :
    e = GlobalTheory.EmbChart.idem τ := by
  obtain ⟨⟨hee, hce, -⟩, hsum, hone⟩ := he
  have hone' : splitProj τ (compFin D.host.F D.host.E v e) = 1 := hone
  have hε := idem_inl_eq_tensAt_one D v

  have h1 : e = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v e) := by
    calc e = GlobalTheory.EmbChart.tensAt D.host.E v 1 * e := by
          rw [← hε, ← hsum, add_mul, hee, mul_comm (cA D e) e, hce, add_zero]
      _ = _ := by rw [GlobalTheory.EmbChart.tensAt_mul_right, one_mul]
  have hc : cA D e = GlobalTheory.EmbChart.tensAt D.host.E v 1 - e := by
    rw [← hε, ← hsum, add_sub_cancel_left]

  have h2 : compFin D.host.F D.host.E v e = splitIdem (isCMExt_host D) τ := by
    apply split_ext (isCMExt_host D) τ
    · rw [splitProj_splitIdem, hone']
    · rw [splitProj_comp_splitIdem, splitProj_comp, compFin_cA, hc, map_sub, GlobalTheory.EmbChart.compFin_tensAt,
        map_sub, map_one, hone', sub_self]
  rw [h1, h2]
  rfl

private theorem eq_of_isIdemAt_of_isIdemAt' {e : AE D} {P Q : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : Formalism.L2.NTheta.IsIdemAt e P) (hQ : Formalism.L2.NTheta.IsIdemAt e Q) : P = Q := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => Q.asIdeal.zero_mem, fun _ => P.asIdeal.zero_mem⟩
  · exact (hP.2 x hx).trans (hQ.2 x hx).symm

theorem exists_emb {e : AE D} {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e PP) :
    ∃ (v : FinPl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), IsIdemOf (D := D) (v := v) (splitProj τ) e ∧ PP = splitPrime τ := by
  obtain ⟨⟨hee, hce, w, ε, ⟨α, rfl, hαw, hαo⟩, hsum⟩, -⟩ := id he

  have hα : α = singleV D.host.F w 1 := by
    classical
    apply RestrictedProduct.ext
    intro u
    by_cases hu : u = w
    · subst hu
      rw [singleV, RestrictedProduct.single_eq_same]
      exact hαw
    · rw [singleV, RestrictedProduct.single_eq_of_ne _ _ hu]
      exact hαo u hu
  subst hα
  have hsum' : e + cA D e = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (.inl w) := hsum
  have hε := idem_inl_eq_tensAt_one D w

  set y := compFin D.host.F D.host.E w e with hy
  have hy1 : y * y = y := by rw [hy, ← map_mul, hee]
  have hy2 : y + sigR _ D.sp.cm.sig y = 1 := by
    rw [hy, compFin_cA, ← map_add (f := _), hsum', hε, GlobalTheory.EmbChart.compFin_tensAt]
  have hσy : sigR _ D.sp.cm.sig y = 1 - y := eq_sub_of_add_eq' hy2

  have hnf : ¬ IsField (Fv D.host.F w ⊗[D.host.F] D.host.E) := by
    intro hf
    by_cases hy0 : y = 0
    · rw [hy0, map_zero, add_zero] at hy2
      exact hf.exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
        hab (by rw [← mul_one a, ← mul_one b, ← hy2, mul_zero, mul_zero])
    · obtain ⟨z, hz⟩ := hf.mul_inv_cancel hy0
      have hy1' : y = 1 := by
        calc y = y * (y * z) := by rw [hz, mul_one]
          _ = y * y * z := by rw [mul_assoc]
          _ = 1 := by rw [hy1, hz]
      rw [hy1', map_one] at hy2
      have h10 : (1 : Fv D.host.F w ⊗[D.host.F] D.host.E) = 0 := add_left_cancel (hy2.trans (add_zero 1).symm)
      exact hf.exists_pair_ne.elim fun a ha => ha.elim fun b hab =>
        hab (by rw [← mul_one a, ← mul_one b, h10, mul_zero, mul_zero])
  have hfin : Module.finrank (Fv D.host.F w) (Fv D.host.F w ⊗[D.host.F] D.host.E) = 2 := by
    rw [Module.finrank_baseChange]
    exact (isCMExt_host D).2.2.1
  obtain ⟨φ₀⟩ := nonempty_algHom_of_not_isField hfin hnf
  obtain ⟨τ₀, rfl⟩ := exists_eq_splitProj (D := D) (v := w) φ₀

  have hτ : ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F w, splitProj τ y = 1 := by
    have hp : IsIdempotentElem (splitProj τ₀ y) := by
      unfold IsIdempotentElem
      rw [← map_mul, hy1]
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hp with h0 | h1
    · refine ⟨τ₀.comp D.sp.cm.sig, ?_⟩
      rw [splitProj_comp, hσy, map_sub, map_one, h0, sub_zero]
    · exact ⟨τ₀, h1⟩
  obtain ⟨τ, hτ⟩ := hτ
  have hi : IsIdemOf (D := D) (v := w) (splitProj τ) e := ⟨he.1, hsum', hτ⟩
  refine ⟨w, τ, hi, ?_⟩

  have he' := he
  rw [eq_idem hi] at he'
  exact eq_of_isIdemAt_of_isIdemAt' he' (GlobalTheory.EmbChart.isIdemAt_idem τ)

theorem idem_dictionary : ∀ (D : D7), (∀ (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (v : FinPl D) (φ : SplitProj D v), IsIdemOf φ e ∧ IsProjAt φ PP) ∧ ∀ (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal ∧ (∀ PP', IsProjAt φ PP' → PP' = PP) ∧ ∀ e, IsIdemOf φ e → Formalism.L2.NTheta.IsIdemAt e PP ∧ (∀ e', Formalism.L2.NTheta.IsIdemAt e' PP → e' = e) ∧ ∀ φ' : SplitProj D v, IsIdemOf φ' e → φ' = φ := by
  intro D
  refine ⟨fun e PP he => ?_, fun v φ PP hφ => ?_⟩
  · obtain ⟨w, τ, hi, rfl⟩ := exists_emb he
    exact ⟨w, splitProj τ, hi, (isProjAt_iff τ _).2 rfl⟩
  · obtain ⟨τ, rfl⟩ := exists_eq_splitProj φ
    obtain rfl : PP = splitPrime τ := (isProjAt_iff τ PP).1 hφ
    refine ⟨(splitPrime_liesOver τ).over.symm, fun PP' h' => (isProjAt_iff τ PP').1 h', fun e he => ?_⟩
    obtain rfl := eq_idem he
    refine ⟨GlobalTheory.EmbChart.isIdemAt_idem τ, fun e' he' => ?_, fun φ' hφ' => ?_⟩
    ·
      obtain ⟨w, τ', hi', hP'⟩ := exists_emb he'
      have hw : w = v := by
        calc w = (splitPrime τ').under (𝓞 D.host.F) := (splitPrime_under τ').symm
          _ = (splitPrime τ).under (𝓞 D.host.F) := by rw [hP']
          _ = v := splitPrime_under τ
      subst hw
      rw [eq_idem hi', splitPrime_injective (isCMExt_host D) hP'.symm]
    ·
      obtain ⟨τ'', rfl⟩ := exists_eq_splitProj φ'
      have h2 := GlobalTheory.EmbChart.isIdemAt_idem τ''
      rw [← eq_idem hφ'] at h2
      rw [splitPrime_injective (isCMExt_host D) (eq_of_isIdemAt_of_isIdemAt' h2 (GlobalTheory.EmbChart.isIdemAt_idem τ))]

end GlobalTheory.SplitIdemDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonBorelJacquetOfCuspidalSegmentJacquet
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.SmGL.CuspSegment

def intervals (l d : ℕ) : (Σ _ : Fin l, Fin d) ≃ Fin (l * d) :=
  (Equiv.sigmaEquivProd _ _).trans finProdFinEquiv

theorem intervals_lt {l d : ℕ} {a b : Fin l} {i j : Fin d}
    (h : intervals l d ⟨a, i⟩ < intervals l d ⟨b, j⟩) : a < b ∨ (a = b ∧ i < j) := by
  have key : (i : ℕ) + d * a < j + d * b := by
    simpa [intervals, finProdFinEquiv, Fin.lt_def] using h
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact Or.inl hab
  · exact Or.inr ⟨rfl, Fin.lt_def.2 (by omega)⟩
  · exfalso
    have h1 : (b : ℕ) + 1 ≤ a := hab
    have h2 : d * ((b : ℕ) + 1) ≤ d * a := Nat.mul_le_mul_left d h1
    have hj := j.isLt
    rw [Nat.mul_succ] at h2
    omega

variable {R : Type} [CommRing R]

theorem unipRad_intervals_le (l d : ℕ) : unipRad R (intervals l d) ≤ unipB R (Fin (l * d)) := by
  intro g hg
  obtain ⟨hpar, hdiag⟩ := mem_unipRad.1 hg
  rw [mem_parab] at hpar
  rw [mem_unipB]
  refine ⟨fun p q hqp => ?_, fun p => ?_⟩
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    obtain ⟨⟨b, j⟩, rfl⟩ := (intervals l d).surjective q
    rcases intervals_lt hqp with hba | ⟨rfl, hji⟩
    · exact hpar _ _ (by simpa using hba)
    · rw [hdiag]
      exact Matrix.one_apply_ne hji.ne'
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    rw [hdiag]
    exact Matrix.one_apply_eq i

theorem leviEmb_intervals_mem {l d : ℕ} (g : Levi R fun _ : Fin l => Fin d)
    (hg : ∀ a, g a ∈ unipB R (Fin d)) : leviEmb R (intervals l d) g ∈ unipB R (Fin (l * d)) := by
  rw [mem_unipB]
  refine ⟨fun p q hqp => ?_, fun p => ?_⟩
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    obtain ⟨⟨b, j⟩, rfl⟩ := (intervals l d).surjective q
    rcases intervals_lt hqp with hba | ⟨rfl, hji⟩
    · exact leviEmb_apply_ne _ _ _ hba.ne' _ _
    · rw [leviEmb_apply_same]
      exact ((mem_unipB (R := R)).1 (hg b)).1 i j hji
  · obtain ⟨⟨a, i⟩, rfl⟩ := (intervals l d).surjective p
    rw [leviEmb_apply_same]
    exact ((mem_unipB (R := R)).1 (hg a)).2 i

theorem twKer_unipB_eq_top {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} (hd : 1 < d) {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin d) k) W} (hσ : IsCuspidal σ) :
    twKer σ (unipB k (Fin d)) 1 = ⊤ := by
  classical
  obtain ⟨-, hcusp⟩ := hσ

  let e : (Σ _ : Fin d, Fin 1) ≃ Fin d := Equiv.sigmaUnique (Fin d) fun _ => Fin 1
  have hblk : ∀ i, blk e i = i := fun i => rfl
  have hne : unipRad k e ≠ ⊥ := by
    rw [CuspMax.unipRad_ne_bot_iff]
    refine ⟨⟨0, by omega⟩, ⟨1, hd⟩, ?_⟩
    rw [hblk, hblk]
    exact Fin.mk_lt_mk.2 Nat.zero_lt_one
  have hsub : Subsingleton (Jacquet σ (unipRad k e)) := hcusp d (fun _ => 1) e hne
  have hB : Subsingleton (Jacquet σ (unipRad k (points (Fin d)))) :=
    CuspMax.subsingleton_jacquet_of_perm σ (e := e) (e' := points (Fin d)) (Equiv.refl _)
      (fun i j h => h) hsub
  exact Submodule.Quotient.subsingleton_iff.1 hB

private theorem deltaHalf_eq_one_of_unipB {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {l d : ℕ} (g : Levi k fun _ : Fin l => Fin d)
    (hg : ∀ a, g a ∈ unipB k (Fin d)) : deltaHalf k (fun _ : Fin l => Fin d) g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [det_eq_one_of_mem_unipRad (hu := (show g a ∈ unipRad k (points (Fin d)) from hg a)), map_one]

theorem subsingleton_jacquet_unipB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (l d : ℕ) (hl : 0 < l) (hd : 1 < d) (V : Type) [AddCommGroup V]
    [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin d) k) W)
    (π : Representation ℂ (GL (Fin (l * d)) k) V) (hσ : IsCuspidal σ)
    (h : ∀ e : (Σ _ : Fin l, Fin d) ≃ Fin (l * d),
      Nonempty ((jac e π).Equiv (piTensor (segTerm σ l)))) :
    Subsingleton (Jacquet π (unipB k (Fin (l * d)))) := by
  classical
  obtain ⟨φ⟩ := h (intervals l d)
  obtain ⟨a₀⟩ : Nonempty (Fin l) := ⟨⟨0, hl⟩⟩
  set K := twKer π (unipB k (Fin (l * d))) 1 with hK

  have hgen : ∀ u ∈ unipB k (Fin (l * d)), ∀ v : V, π u v - v ∈ K := by
    intro u hu v
    exact Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩

  have hUK : twKer π (unipRad k (intervals l d)) 1 ≤ K := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨n, v, rfl⟩
    simpa using hgen n (unipRad_intervals_le l d n.2) v
  let P := Submodule.factor hUK
  have hP : ∀ v : V, P (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := fun v =>
    Submodule.factor_mk hUK v

  have hlevi : ∀ g : Levi k (fun _ : Fin l => Fin d), (∀ a, g a ∈ unipB k (Fin d)) →
      ∀ q, P (jac (intervals l d) π g q) = P q := by
    intro g hg q
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [jac_mk, deltaHalf_eq_one_of_unipB g hg, inv_one, Units.val_one, one_smul, hP, hP]
    exact (Submodule.Quotient.eq _).2 (hgen _ (leviEmb_intervals_mem g hg) v)

  have hfwd : ∀ g z, φ (jac (intervals l d) π g z) = piTensor (segTerm σ l) g (φ z) := by
    intro g z
    have := LinearMap.congr_fun (φ.isIntertwining' g) z
    simpa using this
  have hint : ∀ g y, φ.symm (piTensor (segTerm σ l) g y) = jac (intervals l d) π g (φ.symm y) := by
    intro g y
    apply EquivLike.injective φ
    rw [hfwd, Representation.Equiv.apply_symm_apply, Representation.Equiv.apply_symm_apply]
  let F : (⨂[ℂ] _ : Fin l, W) →ₗ[ℂ] V ⧸ K := P ∘ₗ φ.symm.toLinearMap
  have hFapp : ∀ y, F y = P (φ.symm y) := fun y => rfl
  have hF : ∀ g : Levi k (fun _ : Fin l => Fin d), (∀ a, g a ∈ unipB k (Fin d)) →
      ∀ y, F (piTensor (segTerm σ l) g y) = F y := by
    intro g hg y
    rw [hFapp, hFapp, hint]
    exact hlevi g hg _

  have htop : twKer (segTerm σ l a₀) (unipB k (Fin d)) 1 = ⊤ :=
    twKer_unipB_eq_top hd (LocGL.isCuspidal_twist hσ (LocGL.isSmoothChar_absPow _))
  have htens : ∀ x : Fin l → W, F (PiTensorProduct.tprod ℂ x) = 0 := by
    intro x
    let Lx := (PiTensorProduct.tprod ℂ).toLinearMap x a₀
    have hker : twKer (segTerm σ l a₀) (unipB k (Fin d)) 1 ≤ LinearMap.ker (F ∘ₗ Lx) := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      have hg : ∀ a, (Pi.mulSingle a₀ (u : GL (Fin d) k) : Levi k fun _ : Fin l => Fin d) a ∈
          unipB k (Fin d) := by
        intro a
        by_cases ha : a = a₀
        · rw [ha, Pi.mulSingle_eq_same]
          exact u.2
        · rw [Pi.mulSingle_eq_of_ne ha]
          exact one_mem _
      have hact : Lx (segTerm σ l a₀ u v) =
          piTensor (segTerm σ l) (Pi.mulSingle a₀ (u : GL (Fin d) k)) (Lx v) := by
        simp only [Lx, MultilinearMap.toLinearMap_apply, piTensor_tprod]
        congr 1
        funext a
        by_cases ha : a = a₀
        · rw [ha]
          simp
        · simp [ha]
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, MonoidHom.one_apply,
        Units.val_one, one_smul, map_sub, hact, hF _ hg, sub_self]
    have hx : Lx (x a₀) = PiTensorProduct.tprod ℂ x := by
      simp [Lx]
    rw [← hx]
    exact LinearMap.mem_ker.1 (hker (by rw [htop]; exact Submodule.mem_top))
  have hF0 : F = 0 := PiTensorProduct.ext (MultilinearMap.ext fun x => by simpa using htens x)

  have hv : ∀ v : V, (Submodule.Quotient.mk v : V ⧸ K) = 0 := by
    intro v
    rw [← hP v]
    have hPF : P (Submodule.Quotient.mk v) = F (φ (Submodule.Quotient.mk v)) := by
      rw [hFapp, Representation.Equiv.symm_apply_apply]
    rw [hPF, hF0, LinearMap.zero_apply]
  refine ⟨fun a b => ?_⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact (hv v).trans (hv w).symm

end GlobalTheory.SmGL.CuspSegment
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

variable {D : D7}

def ResAt (c : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ) : Prop :=
  ∀ e : AE D, Formalism.L2.NTheta.IsIdemAt e PP → ∀ x : (AE D)ˣ, e * ((x : AE D) - 1) = (x : AE D) - 1 →
    ∀ (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (u : (kP PP)ˣ),
      (u : kP PP) = resS D.host.F PP ⟨toEAf D (x : AE D), hx⟩ → ((c x : Circle) : ℂ) = ((a u : ℂˣ) : ℂ)

def UnrOff (c : (AE D)ˣ →* Circle) (P : Finset (Pl D.host.E)) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ PP ∈ P, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → UnramAt ε c

theorem ResAt.mul {c c' : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {a a' : (kP PP)ˣ →* ℂˣ} (h : ResAt c PP a)
    (h' : ResAt c' PP a') : ResAt (c * c') PP (a * a') := by
  intro e he x hex hx u hu
  have k := h e he x hex hx u hu
  have k' := h' e he x hex hx u hu
  simp only [MonoidHom.mul_apply, Circle.coe_mul, Units.val_mul, k, k']

theorem ResAt.inv {c : (AE D)ˣ →* Circle} {PP : Pl D.host.E} {a : (kP PP)ˣ →* ℂˣ} (h : ResAt c PP a) :
    ResAt c⁻¹ PP a⁻¹ := by
  intro e he x hex hx u hu
  have k := h e he x hex hx u hu
  simp only [MonoidHom.inv_apply, Circle.coe_inv, Units.val_inv_eq_inv_val, k]

theorem UnrOff.mul {c c' : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} (h : UnrOff c P) (h' : UnrOff c' P) :
    UnrOff (c * c') P := by
  intro v ε hε hv x h₁ h₂ h₃
  rw [MonoidHom.mul_apply, h v ε hε hv x h₁ h₂ h₃, h' v ε hε hv x h₁ h₂ h₃, one_mul]

theorem UnrOff.inv {c : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} (h : UnrOff c P) :
    UnrOff c⁻¹ P := by
  intro v ε hε hv x h₁ h₂ h₃
  rw [MonoidHom.inv_apply, h v ε hε hv x h₁ h₂ h₃, inv_one]

end GlobalTheory.StepLaw

end
end

