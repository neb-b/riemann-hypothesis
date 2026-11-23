module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QIsoAtRight
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.QCalc

section Linear

variable {R A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ : Type} [CommRing R]
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂]
  [Module R A₀] [Module R A₁] [Module R A₂]
  [Module R B₀] [Module R B₁] [Module R B₂]
  [Module R C₀] [Module R C₁] [Module R C₂]
  {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂}
  {c₀ : C₀ →ₗ[R] C₁} {c₁ : C₁ →ₗ[R] C₂}
  {f₀ : A₀ →ₗ[R] B₀} {f₁ : A₁ →ₗ[R] B₁} {f₂ : A₂ →ₗ[R] B₂}
  {g₀ : B₀ →ₗ[R] C₀} {g₁ : B₁ →ₗ[R] C₁} {g₂ : B₂ →ₗ[R] C₂} {k : A₁ →ₗ[R] C₁}

theorem qIsoAt_comp (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x)) (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x))
    (hk : ∀ x, k x = g₁ (f₁ x)) (hf : QIsoAt a₀ a₁ b₀ b₁ f₁) (hg : QIsoAt b₀ b₁ c₀ c₁ g₁) :
    QIsoAt a₀ a₁ c₀ c₁ k := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · have hc : b₁ (f₁ x) = 0 := by rw [← hf₂, hx, map_zero]
    exact hf.1 x hx (hg.1 (f₁ x) hc ⟨y, by rw [hy, hk]⟩)
  · obtain ⟨w, y, hw, hy⟩ := hg.2 z hz
    obtain ⟨x, y', hx, hy'⟩ := hf.2 w hw
    refine ⟨x, y + g₀ y', hx, ?_⟩
    have e : f₁ x = w + b₀ y' := by rw [← hy']; abel
    rw [hk, e, map_add (f := _), hg₀, map_add (f := _), ← hy]
    abel

theorem qIsoAt_right (hf₀ : ∀ x, f₁ (a₀ x) = b₀ (f₀ x)) (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x)) (hk : ∀ x, k x = g₁ (f₁ x))
    (hf : QIsoAt a₀ a₁ b₀ b₁ f₁) (hK : QIsoAt a₀ a₁ c₀ c₁ k) :
    QIsoAt b₀ b₁ c₀ c₁ g₁ := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨u, v, hu, hv⟩ := hf.2 x hx
    have e : f₁ u = x + b₀ v := by rw [← hv]; abel
    obtain ⟨w, hw⟩ := hK.1 u hu ⟨y + g₀ v, by rw [hk, e, map_add (f := _), map_add (f := _), hg₀, hy]⟩
    refine ⟨f₀ w - v, ?_⟩
    rw [map_sub, ← hf₀, hw, e]
    abel
  · obtain ⟨x, y, hx, hy⟩ := hK.2 z hz
    refine ⟨f₁ x, y, by rw [← hf₂, hx, map_zero], ?_⟩
    rw [← hk]
    exact hy

theorem qIsoAt_left (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x)) (hg₂ : ∀ x, g₂ (b₁ x) = c₁ (g₁ x))
    (hk : ∀ x, k x = g₁ (f₁ x))
    (hg : QIsoAt b₀ b₁ c₀ c₁ g₁) (hK : QIsoAt a₀ a₁ c₀ c₁ k) :
    QIsoAt a₀ a₁ b₀ b₁ f₁ := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · exact hK.1 x hx ⟨g₀ y, by rw [← hg₀, hy, hk]⟩
  · have hc : c₁ (g₁ z) = 0 := by rw [← hg₂, hz, map_zero]
    obtain ⟨x, y, hx, hy⟩ := hK.2 (g₁ z) hc
    have hd : b₁ (f₁ x - z) = 0 := by rw [map_sub, ← hf₂, hx, hz, map_zero, sub_zero]
    obtain ⟨y', hy'⟩ := hg.1 (f₁ x - z) hd ⟨y, by rw [map_sub, ← hk, hy]⟩
    exact ⟨x, y', hx, hy'.symm⟩

end Linear

theorem qCalcSt : CxSt → QCalcSt := by
  intro hCx R _ C _ F D E _ _ G H m n k hk
  have cm : ∀ i x, pulln m (i + 1) (dn F i x) = dn G i (pulln m i x) :=
    fun i x ↦ LinearMap.congr_fun ((hCx R C F).2 D G m i) x
  have cn : ∀ i x, pulln n (i + 1) (dn G i x) = dn H i (pulln n i x) :=
    fun i x ↦ LinearMap.congr_fun ((hCx R D G).2 E H n i) x
  have zf : ∀ x : R, pulln m 0 ((0 : R →ₗ[R] Cn F 0) x) =
      (0 : R →ₗ[R] Cn G 0) ((0 : R →ₗ[R] R) x) := fun x ↦ by simp
  have zg : ∀ x : R, pulln n 0 ((0 : R →ₗ[R] Cn G 0) x) =
      (0 : R →ₗ[R] Cn H 0) ((0 : R →ₗ[R] R) x) := fun x ↦ by simp
  refine ⟨fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩, fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩, fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩⟩
  · exact qIsoAt_comp (cm 0) zg (hk 0) h₁.1 h₂.1
  · exact qIsoAt_comp (cm (i + 1)) (cn i) (hk (i + 1)) (h₁.2 i) (h₂.2 i)
  · exact qIsoAt_right zf (cm 0) zg (hk 0) h₁.1 h₂.1
  · exact qIsoAt_right (cm i) (cm (i + 1)) (cn i) (hk (i + 1)) (h₁.2 i) (h₂.2 i)
  · exact qIsoAt_left (cm 0) zg (cn 0) (hk 0) h₁.1 h₂.1
  · exact qIsoAt_left (cm (i + 1)) (cn i) (cn (i + 1)) (hk (i + 1)) (h₁.2 i) (h₂.2 i)

end GlobalTheory.CompanionTheory.QCalc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasiIsomorphismDegreeOneKernel
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal

theorem lid_lTensor_apply {R X Y : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) (u : R ⊗[R] X) :
    TensorProduct.lid R Y (f.lTensor R u) = f (TensorProduct.lid R X u) := by
  induction u with
  | tmul a b => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem univ_coeff : ∀ (R A₀ A₁ A₂ P₀ P₁ P₂ : Type) [CommRing R] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] (d₀ : A₀ →ₗ[R] A₁) (d₁ : A₁ →ₗ[R] A₂) (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] A₀) (ψ₁ : P₁ →ₗ[R] A₁) (ψ₂ : P₂ →ₗ[R] A₂) (r : P₂ →ₗ[R] P₁) (Z : Submodule R A₁) (dZ : A₀ →ₗ[R] Z), (∀ z, z ∈ Z ↔ d₁ z = 0) → (∀ y, (dZ y : A₁) = d₀ y) → a₁ ∘ₗ a₀ = 0 → ψ₁ ∘ₗ a₀ = d₀ ∘ₗ ψ₀ → ψ₂ ∘ₗ a₁ = d₁ ∘ₗ ψ₁ → a₁ ∘ₗ r ∘ₗ a₁ = a₁ → (∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (a₀.lTensor M) (a₁.lTensor M) (d₀.lTensor M) (d₁.lTensor M) (ψ₁.lTensor M)) → ∀ (M : Type) [AddCommGroup M] [Module R M], (∀ x : M ⊗[R] A₁, d₁.lTensor M x = 0 → ∃ (t : M ⊗[R] Z) (y : M ⊗[R] A₀), Z.subtype.lTensor M t + d₀.lTensor M y = x) ∧ (∀ (t : M ⊗[R] Z) (y : M ⊗[R] A₀), Z.subtype.lTensor M t = d₀.lTensor M y → ∃ y' : M ⊗[R] A₀, dZ.lTensor M y' = t) := by
  intro R A₀ A₁ A₂ P₀ P₁ P₂ _ _ _ _ _ _ _ _ _ _ _ _ _ d₀ d₁ a₀ a₁ ψ₀ ψ₁ ψ₂ r Z dZ hZ hdZ haa hc₀ hc₁ hr hQ M _ _
  have hr' : ∀ p, a₁ (r (a₁ p)) = a₁ p := fun p => LinearMap.congr_fun hr p
  have haa' : ∀ p, a₁ (a₀ p) = 0 := fun p => LinearMap.congr_fun haa p
  have hc₀' : ∀ p, ψ₁ (a₀ p) = d₀ (ψ₀ p) := fun p => LinearMap.congr_fun hc₀ p
  have hc₁' : ∀ p, ψ₂ (a₁ p) = d₁ (ψ₁ p) := fun p => LinearMap.congr_fun hc₁ p
  let ε : P₁ →ₗ[R] LinearMap.ker a₁ := (LinearMap.id - r ∘ₗ a₁).codRestrict (LinearMap.ker a₁) (fun p => by
    simp [LinearMap.mem_ker, hr'])
  let ψZ : LinearMap.ker a₁ →ₗ[R] Z := (ψ₁ ∘ₗ (LinearMap.ker a₁).subtype).codRestrict Z (fun p => (hZ _).2 (by
    have hp : a₁ (p : P₁) = 0 := p.2
    simp [← hc₁', hp]))
  let a₀Z : P₀ →ₗ[R] LinearMap.ker a₁ := a₀.codRestrict (LinearMap.ker a₁) (fun p => haa' p)
  have hεs : (LinearMap.ker a₁).subtype ∘ₗ ε = LinearMap.id - r ∘ₗ a₁ := by
    ext p; rfl
  have hει : ε ∘ₗ (LinearMap.ker a₁).subtype = LinearMap.id := by
    ext p
    have hp : a₁ (p : P₁) = 0 := p.2
    simp [ε, hp]
  have hιψ : Z.subtype ∘ₗ ψZ = ψ₁ ∘ₗ (LinearMap.ker a₁).subtype := by
    ext p; rfl
  have hιd : Z.subtype ∘ₗ dZ = d₀ := by
    ext y; exact hdZ y
  have hεa : ε ∘ₗ a₀ = a₀Z := by
    ext p
    show a₀ p - r (a₁ (a₀ p)) = a₀ p
    rw [haa', map_zero, sub_zero]
  have hψa : ψZ ∘ₗ a₀Z = dZ ∘ₗ ψ₀ := by
    ext p
    show ψ₁ (a₀ p) = (dZ (ψ₀ p) : A₁)
    rw [hc₀', hdZ]
  have ha₁ι : a₁ ∘ₗ (LinearMap.ker a₁).subtype = 0 := by
    ext p; exact p.2
  refine ⟨fun x hx => ?_, fun t y h => ?_⟩
  · obtain ⟨w, y, hw, hy⟩ := (hQ M).2 x hx
    have hwε : (LinearMap.ker a₁).subtype.lTensor M (ε.lTensor M w) = w := by
      rw [← LinearMap.lTensor_comp_apply, hεs, LinearMap.lTensor_sub, LinearMap.sub_apply, LinearMap.lTensor_id,
        LinearMap.id_apply, LinearMap.lTensor_comp_apply, hw, map_zero, sub_zero]
    refine ⟨ψZ.lTensor M (ε.lTensor M w), -y, ?_⟩
    rw [← LinearMap.lTensor_comp_apply, hιψ, LinearMap.lTensor_comp_apply, hwε, map_neg, ← hy]
    abel
  · have hsurj : Function.Surjective (ψZ.coprod dZ) := by
      intro z
      obtain ⟨x, y, hx, hy⟩ := (hQ R).2 ((1 : R) ⊗ₜ (z : A₁)) (by simp [(hZ z).1 z.2])
      have e₁ : a₁ (TensorProduct.lid R P₁ x) = 0 := by
        rw [← lid_lTensor_apply, hx, map_zero]
      have e₂ : ψ₁ (TensorProduct.lid R P₁ x) - z = d₀ (TensorProduct.lid R A₀ y) := by
        have := congrArg (TensorProduct.lid R A₁) hy
        rw [map_sub, lid_lTensor_apply, TensorProduct.lid_tmul, one_smul, lid_lTensor_apply] at this
        exact this
      refine ⟨(⟨TensorProduct.lid R P₁ x, e₁⟩, -TensorProduct.lid R A₀ y), Subtype.ext ?_⟩
      have e₃ : ((ψZ ⟨TensorProduct.lid R P₁ x, e₁⟩ : Z) : A₁) = ψ₁ (TensorProduct.lid R P₁ x) := rfl
      simp only [LinearMap.coprod_apply, Submodule.coe_add, e₃, map_neg, Submodule.coe_neg, hdZ, ← e₂]
      abel
    obtain ⟨u, hu⟩ := LinearMap.lTensor_surjective M hsurj t
    have hcop : ψZ.coprod dZ = ψZ ∘ₗ LinearMap.fst R _ _ + dZ ∘ₗ LinearMap.snd R _ _ := by
      ext <;> simp
    obtain ⟨t₁, y₁, ht⟩ : ∃ (t₁ : M ⊗[R] LinearMap.ker a₁) (y₁ : M ⊗[R] A₀),
        t = ψZ.lTensor M t₁ + dZ.lTensor M y₁ := by
      refine ⟨(LinearMap.fst R _ _).lTensor M u, (LinearMap.snd R _ _).lTensor M u, ?_⟩
      rw [← hu, hcop, LinearMap.lTensor_add, LinearMap.add_apply, LinearMap.lTensor_comp_apply,
        LinearMap.lTensor_comp_apply]
    have h1 : Z.subtype.lTensor M (ψZ.lTensor M t₁) = ψ₁.lTensor M ((LinearMap.ker a₁).subtype.lTensor M t₁) := by
      rw [← LinearMap.lTensor_comp_apply, hιψ, LinearMap.lTensor_comp_apply]
    have h2 : Z.subtype.lTensor M (dZ.lTensor M y₁) = d₀.lTensor M y₁ := by
      rw [← LinearMap.lTensor_comp_apply, hιd]
    have hιP : d₀.lTensor M (y - y₁) = ψ₁.lTensor M ((LinearMap.ker a₁).subtype.lTensor M t₁) := by
      rw [map_sub, ← h, ht, map_add (f := _), h1, h2]
      abel
    obtain ⟨p, hp⟩ := (hQ M).1 ((LinearMap.ker a₁).subtype.lTensor M t₁) (by
      rw [← LinearMap.lTensor_comp_apply, ha₁ι, LinearMap.lTensor_zero, LinearMap.zero_apply]) ⟨_, hιP⟩
    have ht₁ : t₁ = a₀Z.lTensor M p := by
      rw [← hεa, LinearMap.lTensor_comp_apply, hp, ← LinearMap.lTensor_comp_apply, hει, LinearMap.lTensor_id,
        LinearMap.id_apply]
    refine ⟨ψ₀.lTensor M p + y₁, ?_⟩
    have h3 : dZ.lTensor M (ψ₀.lTensor M p) = ψZ.lTensor M t₁ := by
      rw [ht₁, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply, hψa]
    rw [map_add (f := _), h3, ← ht]

end GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFil

theorem dividedPowerFiltration_one_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) : pdP δ 1 ≤ J := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hr, rfl⟩
  induction l with
  | nil => simp at hr
  | cons q t ih =>
    have hq : q.2 ∈ J := hl q (by simp)
    rw [List.map_cons, List.prod_cons]
    by_cases h0 : q.1 = 0
    · refine J.mul_mem_left _ (ih (fun q' h' => hl q' (List.mem_cons_of_mem _ h')) ?_)
      simpa [h0] using hr
    · exact J.mul_mem_right _ (δ.dpow_mem h0 hq)

theorem dividedPowerFiltration_mul_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r r' : ℕ) :
    pdP δ r * pdP δ r' ≤ pdP δ (r + r') := by
  unfold pdP
  rw [Ideal.span_mul_span']
  refine Ideal.span_le.2 ?_
  rintro _ ⟨_, ⟨l, hl, hr, rfl⟩, _, ⟨l', hl', hr', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.1 hq with h | h
    · exact hl q h
    · exact hl' q h
  · simpa using Nat.add_le_add hr hr'
  · simp

theorem dpow_mem_pdP {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (k : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow k x ∈ pdP δ k :=
  Ideal.subset_span ⟨[(k, x)], by simpa using hx, by simp, by simp⟩

theorem isFil_sFil : ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)), IsFil (sP Q) (sFil Q) := by
  intro b L Q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr T
    change T.obj.pdPow r.toNat = ⊤
    rw [Int.toNat_of_nonpos hr]
    exact T.obj.pdPow_zero
  · intro T
    change T.obj.pdPow (1 : ℤ).toNat = T.obj.J
    exact le_antisymm (dividedPowerFiltration_one_le T.obj.δ) T.obj.J_le_pdPow_one
  · intro r r' h T
    exact T.obj.pdPow_anti (Int.toNat_le_toNat h)
  · intro r r' T x y hx hy
    have hx' : (show T.obj.B from x) ∈ pdP T.obj.δ r := by
      have : (show T.obj.B from x) ∈ T.obj.pdPow ((r : ℤ).toNat) := hx
      rw [Int.toNat_natCast] at this
      exact this
    have hy' : (show T.obj.B from y) ∈ pdP T.obj.δ r' := by
      have : (show T.obj.B from y) ∈ T.obj.pdPow ((r' : ℤ).toNat) := hy
      rw [Int.toNat_natCast] at this
      exact this
    have h := dividedPowerFiltration_mul_le T.obj.δ r r' (Ideal.mul_mem_mul hx' hy')
    change _ ∈ T.obj.pdPow (((r + r' : ℕ) : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact h
  · intro k T x hx
    change _ ∈ T.obj.pdPow ((k : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact dpow_mem_pdP T.obj.δ k hx

end GlobalTheory.CompanionTheory.DPFil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareZeroNeighbourhoodAffine
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.SectionNbhd

theorem isAffine_subscheme_ker_sq :
    ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (t : U ⟶ Sp R) (e : Sp R ⟶ U)
      [IsClosedImmersion e], e ≫ t = 𝟙 _ → IsAffine (e.ker ^ 2).subscheme := by
  intro R _ U t e _ het
  have hte : ∀ q : Sp R, t (e q) = q := fun q => by
    have := congr($(het) q)
    simpa using this
  set c := (e.ker ^ 2).subschemeι with hc
  have hrange : ∀ x, ∃ q : Sp R, c x = e q := by
    intro x
    have h1 : c x ∈ Set.range c := ⟨x, rfl⟩
    rw [hc, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.support_pow _ _ two_ne_zero, Scheme.Hom.support_ker,
      e.isClosedEmbedding.isClosed_range.closure_eq] at h1
    obtain ⟨q, hq⟩ := h1
    exact ⟨q, hq.symm⟩
  have haff : IsAffineHom (c ≫ t) := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_
    obtain ⟨V₀, hV₀, hyV₀, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := e y) (U := ⊤) trivial
    obtain ⟨f, hfle, hyf⟩ := (isAffineOpen_top (Sp R)).exists_basicOpen_le
      (V := e ⁻¹ᵁ V₀) ⟨y, hyV₀⟩ trivial
    refine ⟨(Sp R).basicOpen f, hyf, (isAffineOpen_top (Sp R)).basicOpen f, ?_⟩
    have hV : IsAffineOpen (V₀ ⊓ t ⁻¹ᵁ (Sp R).basicOpen f) := by
      rw [Scheme.preimage_basicOpen]
      have h := Scheme.basicOpen_res U (V := V₀) (t.app ⊤ f) (homOfLE le_top).op
      rw [← h]
      exact hV₀.basicOpen _
    have heq : (c ≫ t) ⁻¹ᵁ (Sp R).basicOpen f = c ⁻¹ᵁ (V₀ ⊓ t ⁻¹ᵁ (Sp R).basicOpen f) := by
      ext x
      constructor
      · intro hx
        have hx' : t (c x) ∈ (Sp R).basicOpen f := hx
        refine ⟨?_, hx'⟩
        obtain ⟨q, hq⟩ := hrange x
        rw [hq, hte] at hx'
        have : e q ∈ V₀ := hfle hx'
        simpa [hq] using this
      · intro hx
        exact hx.2
    rw [heq]
    exact hV.preimage c
  exact isAffine_of_isAffineHom (c ≫ t)

end GlobalTheory.CompanionTheory.SectionNbhd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareZeroNeighbourhoodProductZero
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.FirstOrderNbhd

theorem comp_app_eq_zero {E T U : Scheme.{0}} (c : E ⟶ U) (i' : T ⟶ E) (W : U.Opens)
    (a' : Γ(U, W)) (a : Γ(E, ⊤)) (h : c.app W a' = E.presheaf.map (homOfLE le_top).op a)
    (ha : i'.appTop a = 0) : (i' ≫ c).app W a' = 0 := by
  have ha0 : i'.app ⊤ a = 0 := ha
  have key : (i' ≫ c).app W a' = i'.app (c ⁻¹ᵁ W) (c.app W a') := by
    rw [Scheme.Hom.comp_app]
    try rfl
  have nat : i'.app (c ⁻¹ᵁ W) (E.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ W ≤ ⊤)).op a)
      = T.presheaf.map (homOfLE (le_top : i' ⁻¹ᵁ c ⁻¹ᵁ W ≤ ⊤)).op (i'.app ⊤ a) := by
    rw [← CategoryTheory.comp_apply, Scheme.Hom.naturality, CategoryTheory.comp_apply]
    try rfl
  rw [key, h, nat, ha0]
  exact map_zero _

theorem exists_mem_ideal_of_lift {T U : Scheme.{0}} (e : T ⟶ U) [QuasiCompact e]
    (i' : T ⟶ (e.ker ^ 2).subscheme) (hi : i' ≫ (e.ker ^ 2).subschemeι = e)
    (W : U.affineOpens) (a : Γ((e.ker ^ 2).subscheme, ⊤)) (ha : i'.appTop a = 0) :
    ∃ a' ∈ e.ker.ideal W, (e.ker ^ 2).subschemeι.app W a' =
      (e.ker ^ 2).subscheme.presheaf.map (homOfLE le_top).op a := by
  obtain ⟨a', ha'⟩ := (e.ker ^ 2).subschemeι_app_surjective W
    ((e.ker ^ 2).subscheme.presheaf.map (homOfLE le_top).op a)
  refine ⟨a', ?_, ha'⟩
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  have h0 := comp_app_eq_zero (e.ker ^ 2).subschemeι i' (W : U.Opens) a' a ha' ha
  rw [hi] at h0
  exact h0

theorem mul_eq_zero_of_lift {T U : Scheme.{0}} (e : T ⟶ U) [QuasiCompact e]
    (i' : T ⟶ (e.ker ^ 2).subscheme) (hi : i' ≫ (e.ker ^ 2).subschemeι = e)
    (a b : Γ((e.ker ^ 2).subscheme, ⊤)) (ha : i'.appTop a = 0) (hb : i'.appTop b = 0) :
    a * b = 0 := by
  refine TopCat.Presheaf.section_ext (e.ker ^ 2).subscheme.sheaf ⊤ (a * b) 0 ?_
  intro x hx
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := (e.ker ^ 2).subschemeι.base x) (U := ⊤) trivial
  let W' : U.affineOpens := ⟨W, hW⟩
  have hxW' : x ∈ (e.ker ^ 2).subschemeι ⁻¹ᵁ (W' : U.Opens) := hxW
  obtain ⟨a', ha'I, ha'⟩ := exists_mem_ideal_of_lift e i' hi W' a ha
  obtain ⟨b', hb'I, hb'⟩ := exists_mem_ideal_of_lift e i' hi W' b hb
  have hab : (e.ker ^ 2).subschemeι.app (W' : U.Opens) (a' * b') = 0 := by
    have hmem : a' * b' ∈ (e.ker ^ 2).ideal W' := by
      rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, sq]
      exact Ideal.mul_mem_mul ha'I hb'I
    rw [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker] at hmem
    exact hmem
  have key : (e.ker ^ 2).subscheme.presheaf.map
      (homOfLE (le_top : (e.ker ^ 2).subschemeι ⁻¹ᵁ (W' : U.Opens) ≤ ⊤)).op (a * b) = 0 := by
    rw [map_mul, ← ha', ← hb', ← map_mul, hab]
  have h1 := TopCat.Presheaf.germ_res_apply (e.ker ^ 2).subscheme.presheaf
    (homOfLE (le_top : (e.ker ^ 2).subschemeι ⁻¹ᵁ (W' : U.Opens) ≤ ⊤)) x hxW' (a * b)
  rw [key, map_zero] at h1
  rw [map_zero]
  exact h1.symm

theorem ideal_sq_zero : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (e : Sp R ⟶ U)
    [IsClosedImmersion e] (i' : Sp R ⟶ (e.ker ^ 2).subscheme),
    i' ≫ (e.ker ^ 2).subschemeι = e → ∀ a b : Γ((e.ker ^ 2).subscheme, ⊤),
    i'.appTop a = 0 → i'.appTop b = 0 → a * b = 0 := by
  intro R _ U e _ i' hi a b ha hb
  exact mul_eq_zero_of_lift e i' hi a b ha hb

end GlobalTheory.CompanionTheory.FirstOrderNbhd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableFamilyProperties
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.StFam

theorem st_all :
    (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (α : ι) ⦃T T' : Thick (nlFun γ p X q κ)⦄ (φ : T ⟶ T'), St Q {U α} T → (∃ β, St Q {U β} T') → St Q {U α} T') ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens), (fun T => ∃ α, St Q {U α} T) = St Q (Set.range U)) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (S : Finset ι), S.Nonempty → capS (fun α => St Q {U α}) S = St Q {⨅ α ∈ S, U α}) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι), capT (fun α => St Q {U α}) i = St Q {capO U i}) := by
  have one : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
      {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}
      (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (V : X.Opens) (T : Thick (nlFun γ p X q κ)),
      St Q {V} T ↔ Q T ∧ InU V T := by
    intro O _ R _ I γ p X q κ Q V T
    constructor
    · rintro ⟨hQ, W, hW, hT⟩
      rw [Set.mem_singleton_iff] at hW
      subst hW
      exact ⟨hQ, hT⟩
    · rintro ⟨hQ, hT⟩
      exact ⟨hQ, V, rfl, hT⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro O _ R _ I γ p X q κ Q ι U α T T' φ h h'
    obtain ⟨β, hβ⟩ := h'
    exact (one Q _ T').2 ⟨((one Q _ T').1 hβ).1, GlobalTheory.CompanionTheory.ThickPt.inU_map (U α) φ ((one Q _ T).1 h).2⟩
  · intro O _ R _ I γ p X q κ Q ι U
    funext T
    refine propext ⟨?_, ?_⟩
    · rintro ⟨α, hα⟩
      obtain ⟨hQ, hT⟩ := (one Q _ T).1 hα
      exact ⟨hQ, U α, ⟨α, rfl⟩, hT⟩
    · rintro ⟨hQ, V, ⟨α, rfl⟩, hT⟩
      exact ⟨α, (one Q _ T).2 ⟨hQ, hT⟩⟩
  · intro O _ R _ I γ p X q κ Q ι U S hS
    funext T
    refine propext ⟨?_, ?_⟩
    · intro h
      obtain ⟨a, ha⟩ := hS
      exact (one Q _ T).2 ⟨((one Q _ T).1 (h a ha)).1,
        (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U S T).2 fun α hα => ((one Q _ T).1 (h α hα)).2⟩
    · intro h α hα
      obtain ⟨hQ, hT⟩ := (one Q _ T).1 h
      exact (one Q _ T).2 ⟨hQ, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U S T).1 hT α hα⟩
  · intro O _ R _ I γ p X q κ Q ι U n i
    have key : ∀ T : Thick (nlFun γ p X q κ), InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
      intro T
      have h := GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun a => U (i a)) (Finset.univ : Finset (Fin (n + 1))) T
      have e : (⨅ a ∈ (Finset.univ : Finset (Fin (n + 1))), U (i a)) = capO U i := by
        simp [capO]
      rw [e] at h
      simpa using h
    funext T
    refine propext ⟨?_, ?_⟩
    · intro h
      exact (one Q _ T).2 ⟨((one Q _ T).1 (h 0)).1, (key T).2 fun a => ((one Q _ T).1 (h a)).2⟩
    · intro h a
      obtain ⟨hQ, hT⟩ := (one Q _ T).1 h
      exact (one Q _ T).2 ⟨hQ, (key T).1 hT a⟩

end GlobalTheory.CompanionTheory.StFam
end

