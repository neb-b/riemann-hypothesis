module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameRescaleConjReductionsDiagonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0206
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0401
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameLiftingPrescribedReductions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead.CyclotomicLifting

variable {D : D7}

theorem adj_mem {R : Type} [CommRing R] (T : Subring R) {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, A i j ∈ T) (i j : Fin n) : A.adjugate i j ∈ T := by
  let A' : Matrix (Fin n) (Fin n) T := fun a b => ⟨A a b, h a b⟩
  have e : T.subtype.mapMatrix A' = A := by ext a b; rfl
  rw [← e, ← RingHom.map_adjugate]
  exact (A'.adjugate i j).2

theorem loc_inv (Q : Pl D.host.E) {n : ℕ} (A : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E))
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hd : Valued.v A.det = 1) :
    ∃ A' : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E), (∀ i j, Valued.v (A' i j) ≤ 1) ∧ A * A' = 1 := by
  have h0 : A.det ≠ 0 := fun h => by rw [h, map_zero] at hd; exact zero_ne_one hd
  refine ⟨A⁻¹, fun i j => ?_, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 h0)⟩
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', map_mul, map_inv₀, hd, inv_one, one_mul]
  have := adj_mem (Q.adicCompletionIntegers D.host.E).toSubring A (fun a b => by
    change A a b ∈ Q.adicCompletionIntegers D.host.E
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hA a b) i j
  change A.adjugate i j ∈ Q.adicCompletionIntegers D.host.E at this
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem glob {n : ℕ} (c c' : ∀ Q : Pl D.host.E, Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E))
    (hc : ∀ Q i j, Valued.v (c Q i j) ≤ 1) (hc' : ∀ Q i j, Valued.v (c' Q i j) ≤ 1) (h1 : ∀ Q, c Q * c' Q = 1) :
    ∃ C : GL (Fin n) (EAf D), (∀ i j, C.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      (∀ i j, (C⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      ∀ Q i j, GlobalTheory.StdFrames.cpt (D := D) Q ((C⁻¹).val i j) = c' Q i j := by
  choose z hzO hz using fun p : Fin n × Fin n => GlobalTheory.AdIsom.exists_of_cpt (D := D) (fun Q => c Q p.1 p.2) (fun Q => hc Q p.1 p.2)
  choose z' hzO' hz' using fun p : Fin n × Fin n => GlobalTheory.AdIsom.exists_of_cpt (D := D) (fun Q => c' Q p.1 p.2) (fun Q => hc' Q p.1 p.2)
  let Z : Matrix (Fin n) (Fin n) (EAf D) := Matrix.of fun i j => z (i, j)
  let Z' : Matrix (Fin n) (Fin n) (EAf D) := Matrix.of fun i j => z' (i, j)
  have hmul : Z * Z' = 1 := by
    ext i j
    refine GlobalTheory.StdFrames.cpt_ext fun Q => ?_
    have e := congrArg (fun M => M i j) (h1 Q)
    simp only [Matrix.mul_apply] at e ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, Z, Z', Matrix.of_apply, hz, hz']
    rw [e, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨⟨Z, Z', hmul, mul_eq_one_comm.1 hmul⟩, fun i j => hzO (i, j), fun i j => hzO' (i, j),
    fun Q i j => hz' (i, j) Q⟩

theorem col_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) (EAf D)) (w : Fin n → Fin n → EAf D) (i j : Fin n) :
    (A * colMat w) i j = Matrix.mulVec A (w j) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat]

theorem res_eq (Q : Pl D.host.E) (x : EAf D) (hmem : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (δ : Formalism.L2.Herm.intAf D.host.F D.host.E) (hcpt : GlobalTheory.StdFrames.cpt Q x = GlobalTheory.StdFrames.cpt Q (δ : EAf D)) :
    Formalism.L2.DIV.resS D.host.F Q ⟨x, hmem⟩ = Formalism.L2.DIV.resS D.host.F Q δ := by
  have e0 : (⟨x, hmem⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨x - δ, sub_mem hmem δ.2⟩ + δ := Subtype.ext (by simp)
  have e1 := (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt (D := D) Q ⟨x - δ, sub_mem hmem δ.2⟩).2 (by
    change Valued.v (GlobalTheory.StdFrames.cpt Q (x - δ)) < 1
    rw [map_sub, hcpt, sub_self, map_zero]
    exact zero_lt_one)
  rw [e0, (Formalism.L2.DIV.resS D.host.F Q).map_add, e1, zero_add]

end GlobalTheory.SeeConjRead.CyclotomicLifting

namespace GlobalTheory.SeeConjRead


set_option maxHeartbeats 1000000 in
open GlobalTheory.SeeConjRead.CyclotomicLifting in
theorem exists_lift_redIs : ∀ {D : D7} {n : ℕ} (β₀ : GL (Fin n) (EAf D)) (S : Finset (Pl D.host.E)) (W : Pl D.host.E → Fin n → Fin n → EAf D), (∀ Q ∈ S, ∀ i j, ((β₀⁻¹).val * colMat (W Q)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ Q ∈ S, Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * colMat (W Q)).det) = 1) → ∃ β : GL (Fin n) (EAf D), GlobalTheory.NormSum.AdLattice.lat β = GlobalTheory.NormSum.AdLattice.lat β₀ ∧ ∀ Q ∈ S, RedIs β Q (W Q) := by
  intro D n β₀ S W hint hdet
  have hloc : ∀ Q : Pl D.host.E, ∃ c c' : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E),
      (∀ i j, Valued.v (c i j) ≤ 1) ∧ (∀ i j, Valued.v (c' i j) ≤ 1) ∧ c * c' = 1 ∧
      (Q ∈ S → c = ((β₀⁻¹).val * colMat (W Q)).map (GlobalTheory.StdFrames.cpt Q)) := by
    intro Q
    by_cases hQ : Q ∈ S
    · have hA : ∀ i j, Valued.v ((((β₀⁻¹).val * colMat (W Q)).map (GlobalTheory.StdFrames.cpt Q)) i j) ≤ 1 :=
        fun i j => (GlobalTheory.AdIsom.mem_OA _).1 (hint Q hQ i j) Q
      have hd : Valued.v (((β₀⁻¹).val * colMat (W Q)).map (GlobalTheory.StdFrames.cpt Q)).det = 1 := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact hdet Q hQ
      obtain ⟨A', hA', h1⟩ := loc_inv Q _ hA hd
      exact ⟨_, A', hA, hA', h1, fun _ => rfl⟩
    · refine ⟨1, 1, fun i j => ?_, fun i j => ?_, one_mul _, fun h => absurd h hQ⟩ <;>
      · rw [Matrix.one_apply]; split_ifs <;> simp
  choose c c' hc hc' h1 hS using hloc
  obtain ⟨C, hCi, hCi', hCc⟩ := glob c c' hc hc' h1
  refine ⟨β₀ * C, le_antisymm (GlobalTheory.NormSum.AdLattice.lat_le_of_int fun i j => ?_)
    (GlobalTheory.NormSum.AdLattice.lat_le_of_int fun i j => ?_), fun Q hQ i j => ?_⟩
  · rw [inv_mul_cancel_left]; exact hCi i j
  · rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]; exact hCi' i j
  have key : Matrix.mulVec ((β₀ * C)⁻¹).val (W Q j) i = ((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j := by
    rw [← Matrix.mul_assoc, col_apply, mul_inv_rev, Units.val_mul]
  rw [key]
  have hmem : ((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hCi' i k) (hint Q hQ k j)
  refine ⟨hmem, ?_⟩
  have hcpt : GlobalTheory.StdFrames.cpt Q (((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    have e : c' Q * c Q = 1 := mul_eq_one_comm.1 (h1 Q)
    rw [hS Q hQ] at e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e, Matrix.mul_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hCc]
    rfl
  split_ifs with hij
  · have h1' : GlobalTheory.StdFrames.cpt Q (((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j) =
        GlobalTheory.StdFrames.cpt Q ((1 : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      rw [hcpt, Matrix.one_apply, if_pos hij]
      exact (map_one _).symm
    exact (res_eq Q _ hmem 1 h1').trans (map_one _)
  · have h0' : GlobalTheory.StdFrames.cpt Q (((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j) =
        GlobalTheory.StdFrames.cpt Q ((0 : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      rw [hcpt, Matrix.one_apply, if_neg hij]
      exact (map_zero _).symm
    exact (res_eq Q _ hmem 0 h0').trans (map_zero _)

end GlobalTheory.SeeConjRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameRescaleConjReductionsDiagonalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_rescale_conj_reductions_diagonal : ∀ {D : D7} {n r : ℕ} (hr : r ≤ n) (β : GL (Fin n) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), IsFrame β Λ → ∀ (Pg : Finset (Pl D.host.E)) (d : ∀ PP : Pl D.host.E, Fin r → (kP PP)ˣ), ∃ β' : GL (Fin n) (EAf D), IsFrame β' Λ ∧ (∀ M, M ∈ St β' ↔ M ∈ St β) ∧ ∀ PP ∈ Pg, ∀ M ∈ St β, upperLeftBlock hr (redFn β' PP M) = (diagGL (d PP))⁻¹ * upperLeftBlock hr (redFn β PP M) * diagGL (d PP) := by
  first | exact @GlobalTheory.FrameRescale.exists_rescale | exact GlobalTheory.FrameRescale.exists_rescale | (intros; apply GlobalTheory.FrameRescale.exists_rescale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeIsogenyFamilyPullbackCorrespondence
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.HeckePoint GlobalTheory.HeckeFrCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem isHkIsog_hkMap (Z : Corr Xo P p i) (hA : admitted l P p) {k : Type} [Field k] [IsAlgClosed k]
    (z : Sp k ⟶ Z.Hk) (C : Subgroup (Over.mk (z ≫ Z.π₁) ⟶ Xo.univ.t.G))
    (hC : Z.toKerScheme.Carries z (z ≫ Z.π₁) C) :
    ∃ ψp, IsHkIsog p (z ≫ Z.π₁) (z ≫ Z.π₂) C ((conj _ _).symm (hkMap Z (h := z) rfl rfl)) ψp := by
  obtain ⟨-, hC⟩ := hC
  have hp : p.Prime := hA.2.2.1
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨⟨hom, hfin, het, hsur, hlin, hiso⟩, hlev⟩ := Z.isog
  have := Xo.smooth
  have := Z.et₁
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  have : IsLocallyNoetherian Z.Hk := LocallyOfFiniteType.isLocallyNoetherian Z.π₁
  obtain ⟨ρ, e₂, e₃, e₄, e₅, e₆⟩ := exists_transfer_pts Z.m₁ z
  obtain ⟨ρ₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_pts Z.m₂ z
  let σ : (Over.mk z ⟶ Z.o₁.t.G) →* (Over.mk z ⟶ Z.o₂.t.G) :=
    MonoidHom.mk' (fun x => x ≫ Z.ψ) fun a c => MonObj.mul_comp a c Z.ψ
  let ψp := ρ₁.toMonoidHom.comp (σ.comp ρ.symm.toMonoidHom)
  have hψ : ∀ x, ψp (ρ x) = ρ₁ (x ≫ Z.ψ) := fun x => congrArg (fun u => ρ₁ (u ≫ Z.ψ)) (ρ.symm_apply_apply x)
  have c₁ := Z.m₁.cart.1
  let α : pullback Xo.univ.t.G.hom (z ≫ Z.π₁) ⟶ Z.o₁.t.G.left := (swap _).inv ≫ hkLift Z z rfl
  have α₁ : α ≫ Z.m₁.cm.F = pullback.fst _ _ := by
    simp only [α, Category.assoc, hkLift_φ, swap_inv_snd]
  have α₂ : α ≫ Z.o₁.t.G.hom = pullback.snd _ _ ≫ z := by
    simp only [α, Category.assoc, hkLift_hom, swap_inv_fst_assoc]
  have hα : ∀ x, fibPt _ (ρ x) ≫ α = x.left := fun x => c₁.hom_ext
    (by rw [Category.assoc, α₁, fibPt, pullback.lift_fst, e₂])
    (by rw [Category.assoc, α₂, fibPt, pullback.lift_snd_assoc, Over.w x]; exact Category.id_comp _)
  have q₁ : (conj _ _).symm (hkMap Z (h := z) rfl rfl) ≫ pullback.fst _ _ = α ≫ Z.ψ.left ≫ Z.m₂.cm.F := by
    show ((swap _).inv ≫ hkMap Z (h := z) rfl rfl ≫ (swap _).hom) ≫ pullback.fst _ _ = _
    simp only [α, Category.assoc, swap_hom_fst, hkMap_snd, hkMap_snd_assoc]
  have q₂ : (conj _ _).symm (hkMap Z (h := z) rfl rfl) ≫ pullback.snd _ _ = pullback.snd _ _ := by
    show ((swap _).inv ≫ hkMap Z (h := z) rfl rfl ≫ (swap _).hom) ≫ pullback.snd _ _ = _
    simp only [Category.assoc, swap_hom_snd, hkMap_fst, hkMap_fst_assoc, swap_inv_fst]
  refine ⟨ψp, by rw [Category.assoc, Category.assoc, Z.base₂], q₂,
    fun x => ?_, fun a x => ?_, fun v => ?_, Subgroup.ext fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    apply pullback.hom_ext
    · rw [Category.assoc, q₁, reassoc_of% hα x, hψ, fibPt, pullback.lift_fst, f₂, Over.comp_left,
        Category.assoc]
    · rw [Category.assoc, q₂, fibPt, fibPt, pullback.lift_snd, pullback.lift_snd]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [← e₃, hψ, hψ, ← f₃, Category.assoc, hlin, Category.assoc]
  · obtain ⟨v, rfl⟩ := ρ₁.surjective v
    obtain ⟨x, rfl⟩ := exists_lift_pt Z.ψ z v
    exact ⟨ρ x, hψ x⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [MonoidHom.mem_ker, hψ, map_eq_one_iff _ ρ₁.injective, Z.ker k z x, hC x _ (e₂ x)]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    obtain ⟨x', rfl⟩ := ρ.surjective x'
    rw [hψ, hψ]
    refine (f₄ _ _ _ _).1 ?_
    replace h := (e₄ _ _ _ _).2 h
    let P₁ := polOf Z.o₁.t Z.o₁.proper Z.o₁.ample Z.o₁.ktriv (ObjDim.smoothOfRelativeDimension Z.o₁)
    let P₂ := polOf Z.o₂.t Z.o₂.proper Z.o₂.ample Z.o₂.ktriv (ObjDim.smoothOfRelativeDimension Z.o₂)
    have hn₀ : 0 < n := Nat.pos_of_ne_zero (by
      rintro rfl
      exact hp.one_lt.ne' ((Nat.coprime_zero_left p).1 hn))
    have : Unique (Over.mk z).left := inferInstanceAs (Unique (PrimeSpectrum k))
    obtain ⟨t₁, t₂⟩ := pow_eq_one_of_weilIs hL.kerPow P₁ hn₀ h
    obtain ⟨c', hc', -⟩ := (hL.weil _ P₂ n _).1 (x ≫ Z.ψ) (x' ≫ Z.ψ)
      (by rw [← MonObj.pow_comp, t₁, MonObj.one_comp]) (by rw [← MonObj.pow_comp, t₂, MonObj.one_comp])
    have e := (weilIs_along_hom hL.globalFns _ _ _ Z.ψ _ _ (p ^ 2) n _ x x' _ _ P₁.isAb P₂.isAb P₁.isLB P₂.isLB hom
      hiso hc').2 h
    rw [unitOn_pow]
    exact e ▸ hc'
  · rw [← e₅, ← e₆, hψ, hψ, Category.assoc, Category.assoc, (hlev p' hp' a).1, (hlev p' hp' a).2, f₅, f₆]
    exact ⟨rfl, rfl⟩

theorem exists_isHeckeFam_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i), admitted l P p → ∀ (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X), x = h ≫ Z.π₁ → x' = h ≫ Z.π₂ → ∃ Ψ : Gx x ⟶ Gx x', IsHeckeFam P p i Ψ ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ Ψ Ψ₁ → Z.toKerScheme.Carries (spMap χ ≫ h) x₁ (transKer Xo.univ.t.G Ψ₁) := by
  intro E _ _ _ H Dw l Xo P p i Z hA T _ h x x' hx hx'
  have hcop : p.Coprime l.M' := (Nat.Prime.coprime_iff_not_dvd hA.2.2.1).2 hA.2.2.2.2
  have hfib : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X)
      (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ (hkMap Z hx hx') Ψ₁ →
        Xo.univ.t.HeckeKer (Over.mk x₁) Dw P p i (transKer Xo.univ.t.G Ψ₁) ∧
          IsHeckeIsog p (transKer Xo.univ.t.G Ψ₁) Ψ₁ ∧
            Z.toKerScheme.Carries (spMap χ ≫ h) x₁ (transKer Xo.univ.t.G Ψ₁) := by
    intro Ω _ _ χ x₁ x₁' Ψ₁ hΨ
    obtain ⟨h₁, h₂, rfl⟩ := isFib_hkMap Z χ hx hx' hΨ
    subst h₁ h₂
    obtain ⟨C, hCk, hCc⟩ := exists_carried Z.toKerScheme (spMap χ ≫ h) _ rfl
    obtain ⟨ψp, hψ⟩ := isHkIsog_hkMap Z hA (spMap χ ≫ h) C ((hCc C).2 rfl)
    have hK := GlobalTheory.ThetaTrace.transKer_of_isHkIsog hψ
    have hH := (isog_iff hcop _ _ C _).1 ⟨ψp, hψ⟩
    rw [Equiv.apply_symm_apply] at hK hH
    rw [hK]
    exact ⟨hCk, hH, (hCc C).2 rfl⟩
  refine ⟨hkMap Z hx hx', ⟨_root_.GlobalTheory.HeckeEx.isLinHom_hkMap_target E H Dw l Xo P p i Z T h x x' hx hx', hkMap_etale Z hx hx',
    hkMap_surjective Z hx hx', ?_, fun Ω _ _ χ x₁ x₁' Ψ₁ hΨ =>
      ⟨(hfib Ω χ x₁ x₁' Ψ₁ hΨ).1, (hfib Ω χ x₁ x₁' Ψ₁ hΨ).2.1⟩⟩,
    fun Ω _ _ χ x₁ x₁' Ψ₁ hΨ => (hfib Ω χ x₁ x₁' Ψ₁ hΨ).2.2⟩
  obtain ⟨β, hβ⟩ := _root_.GlobalTheory.HeckeEx.exists_gen_isoLB E H Dw l Xo P p i Z T h x x' hx hx'
  exact exists_isRigIso_of_isGen _ _ _ _ _ _ _ _ β ⟨hkMap_fst Z hx hx', _root_.GlobalTheory.HeckeEx.hkMap_ptSec_one E H Dw l Xo P p i Z T h x x' hx hx'⟩ hβ

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsVacOfNodeAgree
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem exists_isVac_of_nodeAgree {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}
    {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) {N₁ N₂ : GlobalTheory.Grid.Node D} {X₁ X₂ : GlobalTheory.ChiGrid.Node}
    (h₁ : NodeAgree N₁ W X₁) (h₂ : NodeAgree N₂ W X₂) (f : WO (G'.V X₁) (G'.V X₂) → ℂ)
    (hf : IsVacO W.ψ W.θ (G'.V X₁) (G'.V X₂) (W.cart X₁) (W.cart X₂) (G'.Λ X₁ : Set _) (G'.Λ X₂ : Set _) f) :
    ∃ f' : WO N₁.V N₂.V → ℂ, GlobalTheory.Grid.IsVac W.ψ W.θ false N₁ N₂ f' := by
  obtain ⟨V₁, S₁, M₁, Λ₁, β₁⟩ := N₁
  obtain ⟨V₂, S₂, M₂, Λ₂, β₂⟩ := N₂
  obtain ⟨sp₁, lat₁, cart₁, -⟩ := h₁
  obtain ⟨sp₂, lat₂, cart₂, -⟩ := h₂
  dsimp only at sp₁ sp₂ lat₁ lat₂ cart₁ cart₂
  subst sp₁ sp₂
  cases eq_of_heq lat₁
  cases eq_of_heq lat₂
  refine ⟨f, ?_⟩
  have c₁ := eq_of_heq cart₁
  have c₂ := eq_of_heq cart₂
  unfold GlobalTheory.Grid.IsVac GlobalTheory.Grid.cartS
  simp only [GlobalTheory.Grid.sgnM, cond]
  rw [c₁, c₂]
  exact hf

theorem exists_isVac_col : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ j, j < D.R.m → ∃ f : WO (G.Xp j).V (G.nX j).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ false (G.Xp j) (G.nX j) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hA _ j hj
  have hp : (GlobalTheory.ChiGrid.Pair.top A.μ0 j).InRange D.R.m := by
    simp only [GlobalTheory.ChiGrid.Pair.InRange, GlobalTheory.ChiGrid.Pair.big, GlobalTheory.ChiGrid.Node.InRange]
    omega
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev hp
  obtain ⟨f', hf'⟩ := exists_isVac_of_nodeAgree W (hA.top j hj.le) (hA.top (j + 1) hj) f hf
  rw [hW.ψ, hW.θ] at hf'
  exact ⟨f', hf'⟩

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsVacThRows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GridJoin

theorem isVacO_transport {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) :
    ∀ (S S' S₀ S₀' : HSp D) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (a' : D.what₂.Tau → Matrix (Fin S'.rank) (Fin S'.rank) ℂ)
      (a₀ : D.what₂.Tau → Matrix (Fin S₀.rank) (Fin S₀.rank) ℂ)
      (a₀' : D.what₂.Tau → Matrix (Fin S₀'.rank) (Fin S₀'.rank) ℂ)
      (Λ : Set (Fin S.rank → D.host.E)) (Λ' : Set (Fin S'.rank → D.host.E))
      (Λ₀ : Set (Fin S₀.rank → D.host.E)) (Λ₀' : Set (Fin S₀'.rank → D.host.E)),
      S = S₀ → S' = S₀' → HEq a a₀ → HEq a' a₀' → HEq Λ Λ₀ → HEq Λ' Λ₀' →
      (∃ f, IsVacO ψ θ S₀ S₀' a₀ a₀' Λ₀ Λ₀' f) → ∃ f, IsVacO ψ θ S S' a a' Λ Λ' f := by
  rintro S S' _ _ a a' a₀ a₀' Λ Λ' Λ₀ Λ₀' rfl rfl h1 h2 h3 h4 h
  cases eq_of_heq h1; cases eq_of_heq h2; cases eq_of_heq h3; cases eq_of_heq h4
  exact h

theorem heq_coe_lat {D : D7} {V V' : HSp D} (h : V = V') {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)} (hΛ : HEq Λ Λ') :
    HEq (Λ : Set (Fin V.rank → D.host.E)) (Λ' : Set (Fin V'.rank → D.host.E)) := by
  subst h; cases eq_of_heq hΛ; rfl

theorem exists_isVac_th_rows : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i + 1 ≤ D.R.m → j < D.R.m → ∃ f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hS _ i j hi hj
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .mu A.μ0 (i + 1) j) ⟨hi, by omega⟩
  have a := hS.vert (i + 1) j hi hj.le
  have b := hS.vert (i + 1) (j + 1) hi hj
  rw [← hW.ψ, ← hW.θ]
  exact isVacO_transport W.ψ W.θ _ _ _ _ _ _ _ _ _ _ _ _ a.sp b.sp a.cart b.cart
    (heq_coe_lat a.sp a.lat) (heq_coe_lat b.sp b.lat) ⟨f, hf⟩

end GlobalTheory.GridJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsVacTrueOfAgree
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}

theorem exists_isVac_true_of_agree {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {N₁ N₀ : GlobalTheory.Grid.Node D} {V₁ V₀ : HSp D}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin V₁.rank → D.host.E)} {Λ₀ : Submodule (𝓞 D.host.E) (Fin V₀.rank → D.host.E)}
    {c₁ : D.what₂.Tau → Matrix (Fin V₁.rank) (Fin V₁.rank) ℂ} {c₀ : D.what₂.Tau → Matrix (Fin V₀.rank) (Fin V₀.rank) ℂ}
    (h₁ : N₁.V = V₁) (hΛ₁ : HEq N₁.Λ Λ₁) (hc₁ : HEq (Formalism.IndefR.Links.cart N₁.M) c₁)
    (h₀ : N₀.V = V₀) (hΛ₀ : HEq N₀.Λ Λ₀) (hc₀ : HEq (Formalism.IndefR.Links.cart N₀.M) c₀)
    {f : WO (negSp V₁) V₀ → ℂ} (hf : IsVacO ψ θ (negSp V₁) V₀ (fun τ => -c₁ τ) c₀ (Λ₁ : Set _) (Λ₀ : Set _) f) :
    ∃ f' : WO N₁.V N₀.V → ℂ, GlobalTheory.Grid.IsVac ψ θ true N₁ N₀ f' := by
  subst h₁ h₀
  obtain rfl := eq_of_heq hΛ₁
  obtain rfl := eq_of_heq hΛ₀
  obtain rfl := eq_of_heq hc₁
  obtain rfl := eq_of_heq hc₀
  exact ⟨f, hf⟩

end GlobalTheory.GridJoin

theorem GlobalTheory.GridJoin.exists_isVac_down : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∃ f : WO (G.P (i + 1)).V (G.P i).V → ℂ, GlobalTheory.Grid.IsVac R.ψ R.θ true (G.P (i + 1)) (G.P i) f := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ hsp _ i hi
  obtain ⟨f, hf⟩ := GlobalTheory.FunObj.exists_isVac W hR.lev (p := .core i) (show (GlobalTheory.ChiGrid.Node.core (i + 1)).InRange D.R.m from (by show i + 1 ≤ D.R.m; omega))
  have a₁ := hsp.core (i + 1) (by omega)
  have a₀ := hsp.core i (by omega)
  unfold GlobalTheory.ChiGrid.GridData.Weil.IsVac at hf
  rw [hW.ψ, hW.θ] at hf
  exact GlobalTheory.GridJoin.exists_isVac_true_of_agree a₁.sp a₁.lat a₁.cart a₀.sp a₀.lat a₀.cart hf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniformRealThetaIntertwinerChainStepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformRealThetaIntertwiner_chainStep : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItPair D := by
  first | exact @GlobalTheory.Chain.ItPairObj.itPair_holds | exact GlobalTheory.Chain.ItPairObj.itPair_holds | (intros; apply GlobalTheory.Chain.ItPairObj.itPair_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryMatchingFramesAtNonconjugatePlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_matching_frames_at_nonconjugate_places : ∀ {D : D7} (V : HSp D) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP') → ∀ β₁ β₂ : GL (Fin V.rank) (EAf D), IsFrame β₁ (Formalism.L2.Herm.crdLat V V.L0) → IsFrame β₂ (Formalism.L2.Herm.crdLat V V.L0) → ∃ u ∈ GfC V, IsFrame (finE V u * β₁) (Formalism.L2.Herm.crdLat V V.L0) ∧ ∀ PP ∈ Pg, ∀ x, redFn (finE V u * β₁) PP x = redFn β₂ PP x := by
  first | exact @GlobalTheory.FrameMatch.frames_match | exact GlobalTheory.FrameMatch.frames_match | (intros; apply GlobalTheory.FrameMatch.frames_match <;> assumption)
end

