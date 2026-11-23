module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0171

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionConjugation
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem differentiableAt_entries_exp_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    DifferentiableAt ℝ
      (fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ)) s := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hc : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) _ s :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X s
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  exact (L.hasFDerivAt.comp_hasDerivAt s hc).differentiableAt

theorem dRep_equivariant : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G), π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v) := by
  intro n G H _ _ π hG hrep v hv X hX g hg
  obtain ⟨F, hF, hFv⟩ := hv
  have hu : IsUnit g := hG.isUnit g hg
  have hgi : g⁻¹ ∈ G := hG.inv_mem g hg
  have hinv : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g ((Matrix.isUnit_iff_isUnit_det g).1 hu)
  have hd : DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0 := by
    have he : (fun t : ℝ => π (NormedSpace.exp (t • X)) v) =
        F ∘ fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ) := by
      funext t
      exact hFv _ (hX t)
    rw [he]
    exact (hF.differentiable (by simp)).differentiableAt.comp 0
      (differentiableAt_entries_exp_smul X 0)
  have key : ∀ t : ℝ, π (NormedSpace.exp (t • (g * X * g⁻¹))) (π g v) =
      π g (π (NormedSpace.exp (t • X)) v) := by
    intro t
    have hconj : NormedSpace.exp (t • (g * X * g⁻¹)) = g * NormedSpace.exp (t • X) * g⁻¹ := by
      have : t • (g * X * g⁻¹) = g * (t • X) * g⁻¹ := by
        simp [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
      rw [this, Matrix.exp_conj _ _ hu]
    have hge : g * NormedSpace.exp (t • X) ∈ G := hG.mul_mem _ hg _ (hX t)
    have h1 : π (g * NormedSpace.exp (t • X) * g⁻¹ * g) =
        (π (g * NormedSpace.exp (t • X) * g⁻¹)).comp (π g) :=
      hrep.2 _ (hG.mul_mem _ hge _ hgi) _ hg
    have h2 : g * NormedSpace.exp (t • X) * g⁻¹ * g = g * NormedSpace.exp (t • X) := by
      rw [Matrix.mul_assoc _ g⁻¹ g, hinv, Matrix.mul_one]
    have h3 := hrep.2 _ hg _ (hX t)
    rw [hconj]
    rw [h2, h3] at h1
    exact (DFunLike.congr_fun h1 v).symm
  have h2 := ((π g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt
  have h3 : deriv (fun t : ℝ => π (NormedSpace.exp (t • (g * X * g⁻¹))) (π g v)) 0 =
      π g (deriv (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0) := by
    rw [funext key]
    exact h2.deriv
  exact h3.symm

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVector
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothDeriv

open scoped Matrix.Norms.Operator

variable {n : ℕ}

def coord : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Matrix.of.symm A
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem coord_apply (A : Matrix (Fin n) (Fin n) ℂ) : coord A = Matrix.of.symm A := rfl

theorem hasDerivAt_coord_mul_exp (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => coord (g * NormedSpace.exp (t • X))) (coord (g * X)) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact coord.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h.const_mul g)

theorem contDiff_mul_right (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun z : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of z * X)) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  have e : (fun z : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of z * X) a b) =
      fun z => ∑ c, z a c * X c b := by
    funext z
    simp [Matrix.mul_apply]
  rw [e]
  refine ContDiff.sum fun c _ => ContDiff.mul ?_ contDiff_const
  exact (contDiff_apply ℝ (fun _ => ℂ) c).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) a)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothDeriv

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

open SmoothDeriv

theorem hasDerivAt_dRep_and_isSmoothVec : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G),
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧
      IsSmoothVec G π (dRep π X v) := by
  intro n G H _ _ π hG hrep v hv X hX
  obtain ⟨F, hF, hFG⟩ := hv
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)

  have key : ∀ g ∈ G, HasDerivAt (fun t : ℝ => π g (π (NormedSpace.exp (t • X)) v))
      (fderiv ℝ F (Matrix.of.symm g) (coord (g * X))) 0 := by
    intro g hg
    have h1 := ((hFd (Matrix.of.symm g)).hasFDerivAt)
    have h2 : HasFDerivAt F (fderiv ℝ F (Matrix.of.symm g)) (coord (g * NormedSpace.exp ((0 : ℝ) • X))) := by
      simpa [coord_apply] using h1
    have h3 := h2.comp_hasDerivAt (0 : ℝ) (hasDerivAt_coord_mul_exp g X)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have hm : g * NormedSpace.exp (t • X) ∈ G := hG.mul_mem g hg _ (hX t)
    have := hFG (Matrix.of.symm (g * NormedSpace.exp (t • X))) (by
      rw [Equiv.apply_symm_apply]
      exact hm)
    simp only [Equiv.apply_symm_apply] at this
    simp only [Function.comp, coord_apply]
    rw [← this, hrep.2 g hg _ (hX t)]
    rfl
  have h1 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v)
      (fderiv ℝ F (Matrix.of.symm 1) (coord (1 * X))) 0 := by
    have := key 1 hG.one_mem
    simpa [hrep.1] using this
  have hd : dRep π X v = fderiv ℝ F (Matrix.of.symm 1) (coord (1 * X)) := h1.deriv
  have h1' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 := by
    rw [hd]; exact h1
  refine ⟨h1', fun z => fderiv ℝ F z (Matrix.of.symm (Matrix.of z * X)), ?_, ?_⟩
  · exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_mul_right X)
  · intro z hz
    have h2 := ((π (Matrix.of z)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1'
    exact h2.unique (key _ hz)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsIsotypicSum
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Isotypic

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def IsIrrK (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ IsKStable G π S ∧
    ∀ S' : Submodule ℂ H, S' ≤ S → IsKStable G π S' → S' = ⊥ ∨ S' = S

def isoGens (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) : Set (Submodule ℂ H) :=
  {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k ∈ maxCpt G, ∀ w ∈ S, T (π k w) = π k (T w)}

theorem orthogonal_kstable (hG : IsLinRed G) (hA : IsAdmOn G π) {S : Submodule ℂ H}
    (hS : IsKStable G π S) : IsKStable G π Sᗮ := by
  intro k hk y hy
  rw [Submodule.mem_orthogonal]
  intro s hs
  have hk' : star k ∈ maxCpt G := ⟨hG.star_mem k hk.1, Unitary.star_mem hk.2⟩
  have h1 : π k (π (star k) s) = s := by
    have hm : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk.2
    rw [← ContinuousLinearMap.comp_apply, ← hA.1.2 k hk.1 (star k) hk'.1, hm, hA.1.1]
    rfl
  let Lk : H →ₗᵢ[ℂ] H := ⟨(π k : H →ₗ[ℂ] H), hA.2.2.1 k hk⟩
  have h2 : inner ℂ (π k (π (star k) s)) (π k y) = inner ℂ (π (star k) s) y := Lk.inner_map_map _ _
  rw [← h1, h2]
  exact Submodule.inner_right_of_mem_orthogonal (hS _ hk' s hs) hy

theorem sSup_kstable {A : Set (Submodule ℂ H)} (hA : ∀ S ∈ A, IsKStable G π S) :
    IsKStable G π (sSup A) := by
  intro k hk w hw
  have h : sSup A ≤ (sSup A).comap (π k : H →ₗ[ℂ] H) :=
    sSup_le fun S hS x hx => Submodule.mem_comap.2 (le_sSup hS (hA S hS k hk x hx))
  exact h hw

theorem exists_irr_family (hG : IsLinRed G) (hA : IsAdmOn G π) (m : ℕ) :
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Module.finrank ℂ S = m → IsKStable G π S →
      ∃ F : Set (Submodule ℂ H), F.Finite ∧ (∀ I ∈ F, IsIrrK G π I) ∧ S ≤ sSup F := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hfin hm hS
    by_cases hirr : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStable G π S' → S' = ⊥ ∨ S' = S
    · refine ⟨{S}, Set.finite_singleton S, ?_, ?_⟩
      · rintro I rfl
        exact ⟨hfin, hS, hirr⟩
      · simp
    · push_neg at hirr
      obtain ⟨S', hle, hS', hne0, hneS⟩ := hirr
      haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
      have hlt : S' < S := lt_of_le_of_ne hle hneS
      have hT : IsKStable G π (S ⊓ S'ᗮ) := fun k hk v hv =>
        ⟨hS k hk v hv.1, orthogonal_kstable hG hA hS' k hk v hv.2⟩
      haveI : FiniteDimensional ℂ (S ⊓ S'ᗮ : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_left
      have hltT : S ⊓ S'ᗮ < S := by
        refine lt_of_le_of_ne inf_le_left fun h => hne0 ?_
        have hSo : S ≤ S'ᗮ := inf_eq_left.1 h
        rw [eq_bot_iff]
        intro x hx
        have h0 : ⟪x, x⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hx (hSo (hle hx))
        exact (Submodule.mem_bot ℂ).2 (inner_self_eq_zero.1 h0)
      have hd₁ : Module.finrank ℂ S' < m := hm ▸ Submodule.finrank_lt_finrank_of_lt hlt
      have hd₂ : Module.finrank ℂ (S ⊓ S'ᗮ : Submodule ℂ H) < m :=
        hm ▸ Submodule.finrank_lt_finrank_of_lt hltT
      obtain ⟨F₁, hF₁, hI₁, hle₁⟩ := ih _ hd₁ S' inferInstance rfl hS'
      obtain ⟨F₂, hF₂, hI₂, hle₂⟩ := ih _ hd₂ (S ⊓ S'ᗮ) inferInstance rfl hT
      refine ⟨F₁ ∪ F₂, hF₁.union hF₂, ?_, ?_⟩
      · rintro I (hI | hI)
        · exact hI₁ I hI
        · exact hI₂ I hI
      · intro v hv
        have hp : ((S'.orthogonalProjection v : S') : H) ∈ S' := (S'.orthogonalProjection v).2
        have hq : v - (S'.orthogonalProjection v : H) ∈ S ⊓ S'ᗮ :=
          ⟨S.sub_mem hv (hle hp), Submodule.sub_starProjection_mem_orthogonal (K := S') v⟩
        have e : v = (S'.orthogonalProjection v : H) + (v - (S'.orthogonalProjection v : H)) := by abel
        rw [e, sSup_union]
        exact Submodule.add_mem _ (Submodule.mem_sup_left (hle₁ hp)) (Submodule.mem_sup_right (hle₂ hq))

theorem isoGens_kstable {S S' : Submodule ℂ H} (hS : IsKStable G π S) (h : S' ∈ isoGens G π S) :
    IsKStable G π S' := by
  obtain ⟨T, rfl, hT⟩ := h
  rintro k hk _ ⟨s, hs, rfl⟩
  exact ⟨π k s, hS k hk s hs, hT k hk s hs⟩

theorem le_sSup_isoGens (S : Submodule ℂ H) : S ≤ sSup (isoGens G π S) := by
  refine le_trans (le_of_eq ?_) (le_sSup (show S.map LinearMap.id ∈ isoGens G π S from
    ⟨LinearMap.id, rfl, fun k _ w _ => rfl⟩))
  simp

theorem map_mem_of_gen {Y S S' : Submodule ℂ H} (hSY : sSup (isoGens G π S) ≤ Y) (h : S' ∈ isoGens G π S)
    (D : Y →ₗ[ℂ] H) (hD : ∀ k ∈ maxCpt G, ∀ y y' : Y, (y' : H) = π k y → D y' = π k (D y))
    (hS : IsKStable G π S) {x : H} (hx : x ∈ S') (hxY : x ∈ Y) : D ⟨x, hxY⟩ ∈ Y := by
  obtain ⟨T, rfl, hT⟩ := h
  obtain ⟨s, hs, rfl⟩ := hx
  have hTY : ∀ w ∈ S, T w ∈ Y := fun w hw =>
    hSY (le_sSup (show S.map T ∈ isoGens G π S from ⟨T, rfl, hT⟩) ⟨w, hw, rfl⟩)
  let f : S →ₗ[ℂ] H := D ∘ₗ (T.domRestrict S).codRestrict Y (fun w => hTY w w.2)
  obtain ⟨T', hT'⟩ := LinearMap.exists_extend f
  have hval : ∀ w (hw : w ∈ S), T' w = D ⟨T w, hTY w hw⟩ := fun w hw =>
    LinearMap.congr_fun hT' ⟨w, hw⟩
  have hcomm : ∀ k ∈ maxCpt G, ∀ w ∈ S, T' (π k w) = π k (T' w) := by
    intro k hk w hw
    rw [hval _ (hS k hk w hw), hval w hw]
    exact hD k hk _ _ (hT k hk w hw)
  have hmem : S.map T' ∈ isoGens G π S := ⟨T', rfl, hcomm⟩
  have : T' s ∈ Y := hSY (le_sSup hmem ⟨s, hs, rfl⟩)
  rwa [hval s hs] at this

theorem exists_isotypic_sum : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hA : IsAdmOn G π) {v : H} (hv : IsKFinOn G π v), ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ IsKStable G π Y ∧ ∀ D : Y →ₗ[ℂ] H, (∀ k ∈ maxCpt G, ∀ y y' : Y, (y' : H) = π k y → D y' = π k (D y)) → ∀ y, D y ∈ Y := by
  intro n G H _ _ _ π hG hA v hv
  obtain ⟨S, hfin, hvS, hS⟩ := hv
  obtain ⟨F, hF, hI, hle⟩ := exists_irr_family hG hA _ S hfin rfl hS
  let iso : Submodule ℂ H → Submodule ℂ H := fun I => sSup (isoGens G π I)
  have hisoK : ∀ I ∈ F, IsKStable G π (iso I) := fun I hIF =>
    sSup_kstable fun S' h => isoGens_kstable (hI I hIF).2.1 h
  have hisoF : ∀ I ∈ F, FiniteDimensional ℂ (iso I) := fun I hIF =>
    hA.2.2.2 I (hI I hIF).1 (hI I hIF).2.1 (hI I hIF).2.2
  have hYle : ∀ I ∈ F, iso I ≤ sSup (iso '' F) := fun I hIF => le_sSup ⟨I, hIF, rfl⟩
  refine ⟨sSup (iso '' F), ?_, ?_, ?_, ?_⟩
  · rw [sSup_eq_iSup']
    haveI : Finite ↥(iso '' F) := (hF.image iso).to_subtype
    haveI : ∀ a : ↥(iso '' F), FiniteDimensional ℂ (a : Submodule ℂ H) := by
      rintro ⟨_, I, hIF, rfl⟩
      exact hisoF I hIF
    exact Submodule.finiteDimensional_iSup _
  · exact (sSup_le fun I hIF => (le_sSup_isoGens I).trans (hYle I hIF)) (hle hvS)
  · refine sSup_kstable ?_
    rintro _ ⟨I, hIF, rfl⟩
    exact hisoK I hIF
  · intro D hD y
    have hP : sSup (iso '' F) ≤ ((sSup (iso '' F)).comap D).map (sSup (iso '' F)).subtype := by
      refine sSup_le ?_
      rintro _ ⟨I, hIF, rfl⟩
      refine sSup_le fun S' hS' x hx => ?_
      have hxY : x ∈ sSup (iso '' F) := hYle I hIF (le_sSup hS' hx)
      exact ⟨⟨x, hxY⟩, map_mem_of_gen (hYle I hIF) hS' D hD (hI I hIF).2.1 hx hxY, rfl⟩
    obtain ⟨y', hy', he⟩ := hP y.2
    have hyy : y' = y := Subtype.ext he
    subst hyy
    exact hy'

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Isotypic

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HolomorphicGluingLocalFunctions
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

noncomputable section

namespace GlobalTheory.CompanionTheory.Gaga

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.ChartGlue

variable {X : Scheme.{0}} {s : X ⟶ Sp ℂ} {D : ℕ}

theorem valAt'_eq_ev (U : X.Opens) (f : Γ(X, U)) (y : CxPts s (RingHom.id ℂ)) :
    valAt' y.1 U f = ev s (RingHom.id ℂ) U f y := rfl

theorem comp_eq_id (y : CxPts s (RingHom.id ℂ)) : y.1 ≫ s = 𝟙 _ := by
  rw [y.2]
  simp [spMap]

theorem isHolTo_chart (c : AlgChart s (RingHom.id ℂ) D) (W : X.Opens)
    (ψ : (Fin D → ℂ) ≃L[ℂ] V D) :
    IsHolTo (ψ ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn s (RingHom.id ℂ) W))
      (fun b => (c.e.symm (ψ b)).1) := by
  intro U f
  have hset : ψ ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' (ptsIn s (RingHom.id ℂ) W ∩ ptsIn s (RingHom.id ℂ) U)) =
      {b | b ∈ ψ ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn s (RingHom.id ℂ) W) ∧
        ⊤ ≤ (Opens.map (c.e.symm (ψ b)).1.base).obj U} := by
    ext b
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
  refine ⟨?_, ?_⟩
  · have ho := (c.e.isOpen_inter_preimage_symm
      ((isOpen_ptsIn (p := s) (σ := RingHom.id ℂ) W).inter (isOpen_ptsIn U))).preimage ψ.continuous
    rw [hset] at ho
    exact ho
  · have hd := (c.holo U f).comp
      (ψ.differentiableOn : DifferentiableOn ℂ ψ {b | b ∈ ψ ⁻¹' (c.e.target ∩ c.e.symm ⁻¹' ptsIn s (RingHom.id ℂ) W) ∧
        ⊤ ≤ (Opens.map (c.e.symm (ψ b)).1.base).obj U})
      (fun b hb => ⟨hb.1.1, hb.2⟩)
    refine hd.congr ?_
    intro b _
    exact valAt'_eq_ev U f _

theorem exists_mem_holSec : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D s → ∀ (R : AnRead s (RingHom.id ℂ) D), ∀ (L : LB X), L.IsLB → ∀ h : L.ι → (Sp ℂ ⟶ X) → ℂ, (∀ (i : L.ι) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = 𝟙 _ ∧ ⊤ ≤ y b ⁻¹ᵁ L.U i) → DifferentiableOn ℂ (fun b => h i (y b)) B) → (∀ (i j : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) → h i x = valAt' x (L.U i ⊓ L.U j) (L.g i j).val * h j x) → ∃ σ ∈ R.holSec L, ∀ (i : L.ι), ∀ y ∈ ptsIn s (RingHom.id ℂ) (L.U i), σ i y = h i y.1 := by
  intro X s D _ R L _ h hhol hcoc
  classical
  obtain ⟨ψ⟩ : Nonempty ((Fin D → ℂ) ≃L[ℂ] V D) := ⟨(EuclideanSpace.equiv (Fin D) ℂ).symm⟩
  refine ⟨fun i y => if y ∈ ptsIn s (RingHom.id ℂ) (L.U i) then h i y.1 else 0, ?_, ?_⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i j y hi hj
      have hij : y ∈ ptsIn s (RingHom.id ℂ) (L.U i ⊓ L.U j) := mem_ptsIn_inf.2 ⟨hi, hj⟩
      simp only [if_pos hi, if_pos hj]
      rw [hcoc i j y.1 (comp_eq_id y) hij, valAt'_eq_ev]
      rfl
    · intro i y hy
      simp only [if_neg hy]
    · intro i k
      have hB : IsOpen (ψ ⁻¹' ((R.chart k).e.target ∩
          (R.chart k).e.symm ⁻¹' ptsIn s (RingHom.id ℂ) (L.U i))) :=
        ((R.chart k).e.isOpen_inter_preimage_symm (isOpen_ptsIn _)).preimage ψ.continuous
      have hd := hhol i D _ (fun b => ((R.chart k).e.symm (ψ b)).1) hB
        (isHolTo_chart (R.chart k) (L.U i) ψ) (fun b hb => ⟨comp_eq_id _, hb.2⟩)
      have hd2 := hd.comp ψ.symm.differentiableOn (fun v hv => by
        show ψ (ψ.symm v) ∈ (R.chart k).e.target ∩
          (R.chart k).e.symm ⁻¹' ptsIn s (RingHom.id ℂ) (L.U i)
        rw [ψ.apply_symm_apply]
        exact hv)
      refine hd2.congr ?_
      intro v hv
      have hv2 : (R.chart k).e.symm v ∈ ptsIn s (RingHom.id ℂ) (L.U i) := hv.2
      simp [Function.comp, hv2]
  · intro i y hy
    simp only [if_pos hy]

end GlobalTheory.CompanionTheory.Gaga
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosed
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem lieOf_isLieSubalgebra : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G),
    (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X + Y ∈ HCSS.lieOf G) ∧
    (∀ (r : ℝ) X, X ∈ HCSS.lieOf G → r • X ∈ HCSS.lieOf G) ∧
    (∀ X Y, X ∈ HCSS.lieOf G → Y ∈ HCSS.lieOf G → X * Y - Y * X ∈ HCSS.lieOf G) ∧
    (∀ k ∈ G, ∀ X ∈ HCSS.lieOf G, k * X * k⁻¹ ∈ HCSS.lieOf G) := by
  intro n G hG
  obtain ⟨𝔤, h𝔤, -⟩ := GlobalTheory.CompanionTheory.LinRedLie.exists_lieAlgebra hG
  have hm : ∀ X, X ∈ HCSS.lieOf G ↔ X ∈ 𝔤 := fun X => (h𝔤 X).symm
  refine ⟨fun X Y hX hY => ?_, fun r X hX => ?_, fun X Y hX hY => ?_, fun k hk X hX => ?_⟩
  · exact (hm _).2 (𝔤.add_mem ((hm X).1 hX) ((hm Y).1 hY))
  · exact (hm _).2 (𝔤.smul_mem r ((hm X).1 hX))
  · exact (hm _).2 ((GlobalTheory.CompanionTheory.LieStable.lieAlg_stable hG 𝔤 h𝔤).2 X ((hm X).1 hX) Y ((hm Y).1 hY))
  · exact (hm _).2 (GlobalTheory.CompanionTheory.LieStable.conj_mem hG h𝔤 hk ((hm X).1 hX))

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBound
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord

theorem sum_abs_coord_le_mnorm {n d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hli : LinearIndependent ℝ b) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i) := by
  let L : (Fin d → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun r a c => ∑ i, r i • b i a c
      map_add' := fun r s => by
        funext a c
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun t r => by
        funext a c
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  have hL : ∀ r a c, L r a c = (∑ i, r i • b i) a c := by
    intro r a c
    simp [L, Matrix.sum_apply, Matrix.smul_apply]
  have hker : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun r hr => ?_
    have hsum : ∑ i, r i • b i = 0 := by
      ext a c
      have h := congrFun (congrFun hr a) c
      rw [hL] at h
      simpa using h
    funext i
    exact Fintype.linearIndependent_iff.mp hli r hsum i
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  refine ⟨(d : ℝ) * K, by positivity, fun r => ?_⟩
  have h1 : ‖r‖ ≤ K * ‖L r‖ := by
    have h := hK.le_mul_dist r 0
    simpa [dist_zero_right] using h
  have hN : 0 ≤ GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 : ‖L r‖ ≤ GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by
    refine (pi_norm_le_iff_of_nonneg hN).mpr fun a => ?_
    refine (pi_norm_le_iff_of_nonneg hN).mpr fun c => ?_
    rw [hL]
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm
    calc ‖(∑ i, r i • b i) a c‖ ≤ ∑ c', ‖(∑ i, r i • b i) a c'‖ :=
          Finset.single_le_sum (f := fun c' => ‖(∑ i, r i • b i) a c'‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ c)
      _ ≤ ∑ a', ∑ c', ‖(∑ i, r i • b i) a' c'‖ :=
          Finset.single_le_sum (f := fun a' => ∑ c', ‖(∑ i, r i • b i) a' c'‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have h3 : ∑ i, |r i| ≤ d * ‖r‖ := by
    calc ∑ i, |r i| ≤ ∑ _i : Fin d, ‖r‖ :=
          Finset.sum_le_sum fun i _ => by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm r i
      _ = d * ‖r‖ := by simp
  calc ∑ i, |r i| ≤ d * ‖r‖ := h3
    _ ≤ d * (K * ‖L r‖) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ ≤ d * (K * GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 K.coe_nonneg) (Nat.cast_nonneg _)
    _ = d * K * GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord
end

