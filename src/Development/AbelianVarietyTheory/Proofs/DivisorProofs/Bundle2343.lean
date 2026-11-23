module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOfMatRel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.DiagMat

def act (M : Matrix (Fin 8) (Fin 8) ℤ) (X : Type) [AddCommGroup X] : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun c := fun v => ∑ u, M v u • c u
  map_zero' := by ext v; simp
  map_add' c d := by ext v; simp [smul_add, Finset.sum_add_distrib]

theorem act_apply (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (c : Fin 8 → X) (v : Fin 8) :
    act M X c v = ∑ u, M v u • c u := rfl

theorem act_act (M N : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (c : Fin 8 → X) :
    act M X (act N X c) = act (M * N) X c := by
  ext v
  simp only [act_apply, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

theorem act_one {X : Type} [AddCommGroup X] (c : Fin 8 → X) : act 1 X c = c := by
  ext v
  simp [act_apply, Matrix.one_apply]

theorem act_comp {X₀ X₁ : Type} [AddCommGroup X₀] [AddCommGroup X₁] (M : Matrix (Fin 8) (Fin 8) ℤ)
    (π : X₀ →+ X₁) (c : Fin 8 → X₀) : act M X₁ (fun u => π (c u)) = fun u => π (act M X₀ c u) := by
  ext v
  set_option synthInstance.maxHeartbeats 100000 in
    simp [act_apply, map_sum, map_zsmul]

theorem matRel_iff (W : Matrix (Fin 8) (Fin 8) ℤ) {X : Type} [AddCommGroup X] (a b : Fin 8) (y y' : Fin 8 → X) :
    MatRel W a b y y' ↔ act (W + W.transpose) X y' = Pi.single b (act (W + W.transpose) X y a) := by
  constructor
  · intro h; ext v; rw [act_apply, h v, Pi.single_apply]; rfl
  · intro h v; have := congrFun h v; rw [act_apply] at this; rw [this, Pi.single_apply]; rfl

end GlobalTheory.Poinc.Eq8.DiagMat


open GlobalTheory.Poinc.Eq8.DiagMat in
theorem GlobalTheory.Poinc.Eq8.exists_diag_of_matRel : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (Y X₀ X₁ : Type) [AddCommGroup Y] [AddCommGroup X₀] [AddCommGroup X₁] (m : Fin 8 → Fin 8 → (Y →+ Y)) (e₀ : Y ≃+ (Fin 8 → X₀)) (ρ : Y →+ (Fin 8 → X₁)), Function.Surjective ρ → (∀ a b y, MatRel W a b (e₀ y) (e₀ (m a b y))) → (∀ a b y, MatRel W a b (ρ y) (ρ (m a b y))) → ∃ π : X₀ →+ X₁, Function.Surjective π ∧ ∀ y u, ρ y u = π (e₀ y u) := by
  intro W hW Y X₀ X₁ _ _ _ m e₀ ρ hρ h₀ h₁
  set Q := W + W.transpose with hQ
  have hdet : IsUnit Q.det := by rw [hW.2]; exact isUnit_one
  have hQP : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hdet
  have hPQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hdet

  let Ψ : (Fin 8 → X₀) →+ (Fin 8 → X₁) :=
    (act Q X₁).comp (ρ.comp ((e₀.symm : (Fin 8 → X₀) →+ Y).comp (act Q⁻¹ X₀)))
  have hΨ : ∀ z, Ψ (act Q X₀ (e₀ z)) = act Q X₁ (ρ z) := by
    intro z
    simp only [Ψ, AddMonoidHom.comp_apply, act_act, hPQ, act_one]
    simp
  have hE : ∀ a b c, Ψ (Pi.single b (c a)) = Pi.single b (Ψ c a) := by
    intro a b c
    set z := e₀.symm (act Q⁻¹ X₀ c) with hz
    have hc : act Q X₀ (e₀ z) = c := by simp [hz, act_act, hQP, act_one]
    have r0 := (matRel_iff W a b _ _).1 (h₀ a b z)
    have r1 := (matRel_iff W a b _ _).1 (h₁ a b z)
    rw [← hQ, hc] at r0
    rw [← hQ] at r1
    rw [← r0, hΨ, r1, ← hΨ, hc]
  let π : X₀ →+ X₁ := (Pi.evalAddMonoidHom (fun _ => X₁) 0).comp (Ψ.comp (AddMonoidHom.single (fun _ => X₀) 0))
  have hπ : ∀ b x, Ψ (Pi.single b x) = Pi.single b (π x) := by
    intro b x
    have := hE 0 b (Pi.single 0 x)
    simpa [π] using this
  have hdiag : ∀ c, Ψ c = fun u => π (c u) := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hπ]
    rw [← Finset.univ_sum_single (fun u => π (c u))]
  have key : ∀ y u, ρ y u = π (e₀ y u) := by
    intro y u
    have h1 : act Q X₁ (ρ y) = fun u => π (act Q X₀ (e₀ y) u) := by rw [← hΨ, hdiag]
    have h2 := congrArg (act Q⁻¹ X₁) h1
    rw [act_act, hPQ, act_one, act_comp, act_act, hPQ, act_one] at h2
    exact congrFun h2 u
  refine ⟨π, ?_, key⟩
  intro x
  obtain ⟨y, hy⟩ := hρ (fun _ => x)
  exact ⟨e₀ y 0, by rw [← key, hy]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenCoordinatesIdempotentRangeQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory

theorem exists_eigen_coordinates_range_quot : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C), I ^ 2 = ⊥ →
  ∀ {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H]
  (σ : A →+* Module.End C H) (a : ℕ) (χ : Fin a → A →+* C),
  (∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤) →
  ∀ (π : Module.End C H), π * π = π → (∀ c, σ c * π = π * σ c) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ c, ∀ x ∈ F, σ c x ∈ F) → (∀ x ∈ F, π x ∈ F) →
  (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) →
  (∀ d ∈ LinearMap.range π, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ F) ∧ d - ∑ i, w i ∈ F) →
  ∃ (n : ℕ) (κ : Fin n → Fin a) (ℓ : Fin n → H →ₗ[C] C ⧸ I) (y : Fin n → H),
    (∀ k c x, ℓ k (σ c x) = Ideal.Quotient.mk I (χ (κ k) c) * ℓ k x) ∧
    (∀ x ∈ LinearMap.range π, x ∈ F ↔ ∀ k, ℓ k x = 0) ∧
    (∀ k, y k ∈ LinearMap.range π) ∧ ∀ j k, ℓ j (y k) = if j = k then 1 else 0 := by
  intro C _ _ I hI2 A _ H _ _ _ _ σ a χ hχ π hπ hσπ F hIF hσF hπF hEM hdec
  have hItop : I ≠ ⊤ := by
    rintro rfl
    rw [Ideal.top_pow] at hI2
    exact top_ne_bot hI2
  obtain ⟨m, s, r, hrs⟩ := _root_.GlobalTheory.quotient_retract_pi_quotient I F hIF hEM
  let σb : A →+* Module.End C (H ⧸ F) :=
    { toFun := fun c => F.mapQ F (σ c) (fun x hx => hσF c x hx)
      map_one' := Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp)
      map_mul' := fun c d => Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp)
      map_zero' := Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp)
      map_add' := fun c d => Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp) }
  have hσb : ∀ c x, σb c (F.mkQ x) = F.mkQ (σ c x) := fun c x => rfl
  let πb : Module.End C (H ⧸ F) := F.mapQ F π (fun x hx => hπF x hx)
  have hπb : ∀ x, πb (F.mkQ x) = F.mkQ (π x) := fun x => rfl
  have hπσ : ∀ c, πb * σb c = σb c * πb := fun c => Submodule.linearMap_qext _ (LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, Module.End.mul_apply, hσb, hπb]
    rw [← Module.End.mul_apply, ← hσπ c, Module.End.mul_apply])
  have hσσ : ∀ c d, σb c * σb d = σb d * σb c := fun c d => by
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨e, he1, he2, he3⟩ := _root_.GlobalTheory.eigenIdempotents_of_comaximal σb a χ hχ
  have heπ : ∀ i, πb * e i = e i * πb := fun i => he1 i πb hπσ
  have heσ : ∀ i c, σb c * e i = e i * σb c := fun i c => he1 i (σb c) (hσσ c)
  have hππ : πb * πb = πb := Submodule.linearMap_qext _ (LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, Module.End.mul_apply, hπb]
    rw [← Module.End.mul_apply, hπ])

  have hD : ∀ x ∈ LinearMap.range π, ∃ u : Fin a → H ⧸ F, (∀ i c, σb c (u i) = χ i c • u i) ∧
      F.mkQ x = ∑ i, u i := by
    intro x hx
    obtain ⟨w, hw1, hw2⟩ := hdec x hx
    refine ⟨fun i => F.mkQ (w i), fun i c => ?_, ?_⟩
    · rw [hσb, ← map_smul, ← sub_eq_zero, ← map_sub]
      exact (Submodule.Quotient.mk_eq_zero F).2 (hw1 i c)
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← sub_eq_zero, ← map_sub]
      exact (Submodule.Quotient.mk_eq_zero F).2 hw2
  have hEu : ∀ x ∈ LinearMap.range π, ∀ u : Fin a → H ⧸ F, (∀ i c, σb c (u i) = χ i c • u i) →
      F.mkQ x = ∑ i, u i → ∀ i, e i (F.mkQ x) = u i := by
    intro x hx u hu hxu i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxu, map_sum, Finset.sum_eq_single i]
    · exact he2 i (u i) (hu i)
    · intro j _ hji; exact he3 i j (u j) hji (hu j)
    · simp
  let p : Fin a → Module.End C (H ⧸ F) := fun i => e i * πb
  have hpx : ∀ i x, p i (F.mkQ x) = e i (F.mkQ (π x)) := fun i x => rfl
  have hpσ : ∀ i c, p i * σb c = σb c * p i := fun i c => by
    simp only [p]; rw [_root_.mul_assoc, hπσ, ← _root_.mul_assoc, ← heσ, _root_.mul_assoc]

  have hpE : ∀ i w, ∀ c, σb c (p i w) = χ i c • p i w := by
    intro i w c
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective F w
    obtain ⟨u, hu, hxu⟩ := hD (π x) (LinearMap.mem_range_self π x)
    rw [hpx, hEu _ (LinearMap.mem_range_self π x) u hu hxu]
    exact hu i c
  have hpe : ∀ i w, (∀ c, σb c w = χ i c • w) → e i (p i w) = p i w := fun i w _ => he2 i _ (hpE i w)
  have hpπ : ∀ i w, πb (p i w) = p i w := by
    intro i w
    simp only [p]
    rw [← Module.End.mul_apply, ← _root_.mul_assoc, heπ, _root_.mul_assoc, hππ]
  have hpp : ∀ i j w, p j (p i w) = if j = i then p i w else 0 := by
    intro i j w
    show e j (πb (p i w)) = _
    rw [hpπ]
    split_ifs with h
    · subst h; exact he2 j _ (hpE j w)
    · exact he3 j i _ (Ne.symm h) (hpE i w)
  have hidem : ∀ i, p i * p i = p i := fun i => LinearMap.ext fun w => by
    rw [Module.End.mul_apply, hpp]; simp
  choose n b f hb hfp hδ hinj using fun i => _root_.GlobalTheory.idem_retract_coords I hItop m s r hrs (p i) (hidem i)
  obtain ⟨eqv⟩ : Nonempty ((Σ i, Fin (n i)) ≃ Fin (∑ i, n i)) := ⟨finSigmaFinEquiv⟩
  have hlift : ∀ i t, ∃ z ∈ LinearMap.range π, F.mkQ z = b i t := by
    intro i t
    obtain ⟨w, hw⟩ := hb i t
    obtain ⟨h', hh'⟩ := Submodule.mkQ_surjective F (e i w)
    refine ⟨π h', LinearMap.mem_range_self π h', ?_⟩
    rw [← hw, ← hπb, hh']
    show πb (e i w) = (e i * πb) w
    rw [← Module.End.mul_apply, heπ]
  choose z hz hzb using hlift
  let L : (Σ i, Fin (n i)) → H →ₗ[C] C ⧸ I := fun q => f q.1 q.2 ∘ₗ F.mkQ
  let Z : (Σ i, Fin (n i)) → H := fun q => z q.1 q.2
  have hL : ∀ i t x, L ⟨i, t⟩ x = f i t (F.mkQ x) := fun _ _ _ => rfl
  have hZ : ∀ i t, Z ⟨i, t⟩ = z i t := fun _ _ => rfl
  refine ⟨∑ i, n i, fun k => (eqv.symm k).1, fun k => L (eqv.symm k),
    fun k => Z (eqv.symm k), ?_, ?_, fun k => hz _ _, ?_⟩
  · intro k c x
    obtain ⟨⟨i, t⟩, rfl⟩ := eqv.surjective k
    simp only [Equiv.symm_apply_apply, hL]
    rw [← hσb, ← hfp i t, ← Module.End.mul_apply, hpσ, Module.End.mul_apply, hpE, map_smul, hfp,
      Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  · intro x hx
    constructor
    · intro hxF k
      have h0 : F.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero F).2 hxF
      simp only [L, LinearMap.comp_apply, h0, map_zero]
    · intro hk
      obtain ⟨u, hu, hxu⟩ := hD x hx
      have hpu : ∀ i, p i (F.mkQ x) = u i := by
        intro i
        obtain ⟨x', rfl⟩ := hx
        have hx' : π (π x') = π x' := by rw [← Module.End.mul_apply, hπ]
        rw [hpx, hx']
        exact hEu _ (LinearMap.mem_range_self π x') u hu hxu i
      have h0 : ∀ i, u i = 0 := by
        intro i
        rw [← hpu i]
        refine hinj i _ (LinearMap.mem_range_self _ _) fun t => ?_
        rw [hfp]
        simpa [hL] using hk (eqv ⟨i, t⟩)
      rw [← Submodule.Quotient.mk_eq_zero F]
      change F.mkQ x = 0
      rw [hxu]; simp [h0]
  · intro j k
    obtain ⟨⟨i', t'⟩, rfl⟩ := eqv.surjective j
    obtain ⟨⟨i, t⟩, rfl⟩ := eqv.surjective k
    simp only [Equiv.symm_apply_apply, hL, hZ, hzb, eqv.injective.eq_iff]
    by_cases hii : i' = i
    · subst hii
      rw [hδ]
      simp
    · have : f i' t' (b i t) = 0 := by
        obtain ⟨w, hw⟩ := hb i t
        rw [← hfp, ← hw, hpp, if_neg hii, map_zero]
      rw [this, if_neg]
      intro h; exact hii (congrArg Sigma.fst h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TorUniq

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem eq_zero_of_forall_dvd {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {l : ℕ} (hl : 2 ≤ l)
    (v : X) (h : ∀ n : ℕ, ∃ z : X, v = (l ^ n) • z) : v = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  refine b.repr.injective ?_
  rw [map_zero]
  ext i
  rw [Finsupp.zero_apply]
  obtain ⟨N, hN⟩ : ∃ N, N = (b.repr v i).natAbs := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ := h N
  have hd : ((l ^ N : ℕ) : ℤ) ∣ b.repr v i :=
    ⟨b.repr z i, by rw [hz, ← natCast_zsmul, map_zsmul, Finsupp.smul_apply, smul_eq_mul]⟩
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd ?_
  rw [Int.natAbs_natCast, ← hN]
  exact Nat.lt_pow_self (by omega)

theorem exists_eq_add_nsmul {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {F : Type} [Field F]
    {k : ℕ} {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ k) {u v : X}
    (h : ∀ τ : Multiplicative X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd u) = τ (Multiplicative.ofAdd v)) :
    ∃ z : X, v = u + k • z := by
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ i, ∃ c : ℤ, b.repr (v - u) i = k * c := fun i => by
    let τ : Multiplicative X →* Fˣ := (zpowersHom Fˣ ζ).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
    have e : ζ ^ (b.repr u i) = ζ ^ (b.repr v i) := h τ (MonoidHom.ext fun x => by
      show (ζ ^ (b.coord i x.toAdd)) ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow])
    refine (hζ.zpow_eq_one_iff_dvd _).1 ?_
    rw [map_sub, Finsupp.sub_apply, zpow_sub, e, mul_inv_cancel]
  choose c hc using key
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [← sub_eq_iff_eq_add', ← b.sum_repr (v - u), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hc, mul_smul, natCast_zsmul]

end GlobalTheory.Poinc.TorUniq

namespace GlobalTheory.Poinc.Eq8

open GlobalTheory.Poinc.TorUniq

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem torMatch_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → ∀ ρ ρ', TorMatch U U' g β ρ → TorMatch U U' g β ρ' → ρ = ρ' := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hg ρ ρ' h h'
  have hL := GlobalTheory.firstFiveLaws
  let gK : FractionRing R →+* FractionRing V := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V (FractionRing V)).comp hg)
  have hgK : ∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r) := IsFractionRing.lift_algebraMap _
  let F := AlgebraicClosure (FractionRing V)
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing V) F).comp gK).toAlgebra
  have hF : ∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r)) :=
    fun r => congrArg (algebraMap (FractionRing V) F) (hgK r)

  have img : ∀ {S : Type} [CommRing S] [IsDomain S] [IsLocalRing S], GlobalTheory.Mum.Base S → ∀ {H : Over (Sp S)} [GrpObj H]
      [IsCommMonObj H], IsSemiAbelian H → ∀ {E : DegData S (maximalIdeal S)} {B : PolAV (Sp (FractionRing S))}
      (W : Unif (maximalIdeal S) E B H) [Algebra (FractionRing S) F] (k : ℕ), 1 ≤ k → ∀ p : QkPt E.toPre F k,
      ∃ x : TFK (R := S) F ⟶ B.A, QkToAkU W.toUnifPre F k p x := by
    intro S _ _ _ hS H _ _ hH E B W _ k hk p
    obtain ⟨x, hx⟩ := GlobalTheory.TorsionAnyChar.existsTransl_any hL S (maximalIdeal S) hS.1 E B H hH W F k hk p
    exact ⟨x, (GlobalTheory.TorsionAnyChar.indAtTransl_any hL S (maximalIdeal S) hS.1 E B H hH W F k hk p x).1
      (hx 1 k le_rfl (mul_one k).symm p (one_smul _ _).symm rfl)⟩

  have key : ∀ k : ℕ, IsUnit (k : R) → ∀ τ' : Multiplicative D'.toPre.X →* Fˣ, τ' ^ k = 1 →
      ∀ χ, τ' (Multiplicative.ofAdd (ρ χ)) = τ' (Multiplicative.ofAdd (ρ' χ)) := by
    intro k hk τ' hτ' χ
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
    let τ₁ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ)
    let τ₂ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ')
    obtain ⟨q₁, y₁, t₁⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult (F := F) (k := k) τ₁
      (MonoidHom.ext fun χ => DFunLike.congr_fun hτ' _)
    obtain ⟨q₂, y₂, t₂⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult (F := F) (k := k) τ₂
      (MonoidHom.ext fun χ => DFunLike.congr_fun hτ' _)
    obtain ⟨q', y', t'⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D'.tau_bimult (F := F) (k := k) τ' hτ'
    obtain ⟨a₁, ha₁⟩ := img hR hG U k hk1 q₁
    obtain ⟨a₂, ha₂⟩ := img hR hG U k hk1 q₂
    obtain ⟨a', ha'⟩ := img hV hG' U' k hk1 q'
    have e₁ := h F hF k hk τ₁ τ' q₁ q' a₁ a' hτ' (fun _ => rfl) y₁ t₁ y' t' ha₁ ha'
    have e₂ := h' F hF k hk τ₂ τ' q₂ q' a₂ a' hτ' (fun _ => rfl) y₂ t₂ y' t' ha₂ ha'
    have e : a₁.left ≫ genMap U = a₂.left ≫ genMap U := e₁.trans e₂.symm

    have ea : a₁ = a₂ := by
      refine Over.OverMorphism.ext ?_
      have e' : a₁.left ≫ U.gen.inv.left = a₂.left ≫ U.gen.inv.left := by
        refine pullback.hom_ext ?_ ?_
        · simpa only [genMap, Category.assoc] using e
        · have w₁ := Over.w U.gen.inv
          have s : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := w₁
          rw [Category.assoc, Category.assoc, s, Over.w a₁, Over.w a₂]
      simpa using congrArg (· ≫ U.gen.hom.left) e'
    subst ea
    obtain ⟨z, hz, hh, hι, hadd⟩ := GlobalTheory.TorsionMapInj.qkToAk_injective_closed R (maximalIdeal R) hR.1 D A G hG U F k hk1
      q₁ q₂ a₁ ha₁ ha₂
    have hz0 : z = 0 := by
      rw [y₁, y₂, zero_add, eq_comm, ← natCast_zsmul] at hz
      exact (smul_eq_zero.1 hz).resolve_left (by exact_mod_cast hk0)
    subst hz0
    rw [GlobalTheory.TorusExt.isIota_iff_eq D.tau_bimult, map_zero] at hι
    subst hι
    rw [GlobalTheory.TorusExt.isAdd_iff_eq, add_zero] at hadd
    rw [hadd] at t₂
    have u := ((GlobalTheory.TorsionAnyChar.gtOnto_any hL R (maximalIdeal R) hR.1 D F).2.2.2.1 q₁.g t₁.1).unique t₁ t₂
    exact congrArg Units.val (DFunLike.congr_fun u (Multiplicative.ofAdd χ)) |> Units.ext
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  refine AddMonoidHom.ext fun χ => ?_
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_dvd hl2 _ fun n => ?_
  have hk : IsUnit ((l ^ n : ℕ) : R) := by simpa using hl.pow n
  have hkF : ((l ^ n : ℕ) : F) ≠ 0 := by
    have := hk.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))
    rw [map_natCast] at this
    exact this.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : F) := ⟨hkF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (l ^ n)
  have hn0 : l ^ n ≠ 0 := pow_ne_zero _ (by omega)
  obtain ⟨z, hz⟩ := exists_eq_add_nsmul (ζ := (hζ.isUnit hn0).unit) (IsPrimitiveRoot.coe_units_iff.1 hζ)
    (key (l ^ n) hk · · χ)
  exact ⟨-z, by rw [hz, smul_neg]; abel⟩

end GlobalTheory.Poinc.Eq8
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantLiftFunctionalQuotientProjectiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory

theorem eqLift_tensorModOf : ∀ {C : Type} [CommRing C] (I : Ideal C) {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H]
  (σ : A →+* Module.End C H), (letI := GlobalTheory.HTSummand.tensorModOf σ; Module.Projective (C ⊗[ℤ] A) H) →
  ∀ (χ : A →+* C) (l₀ : H →ₗ[C] C ⧸ I), (∀ a x, l₀ (σ a x) = Ideal.Quotient.mk I (χ a) * l₀ x) →
  ∃ l : H →ₗ[C] C, (∀ a x, l (σ a x) = χ a * l x) ∧ ∀ x, Ideal.Quotient.mk I (l x) = l₀ x := by
  intro C _ I A _ H _ _ σ hproj χ l₀ hl₀
  letI mH : Module (C ⊗[ℤ] A) H := GlobalTheory.HTSummand.tensorModOf σ
  let χt : C ⊗[ℤ] A →ₐ[ℤ] C := Algebra.TensorProduct.productMap (AlgHom.id ℤ C) χ.toIntAlgHom
  have hχt : ∀ (r : C) (a : A), χt (r ⊗ₜ[ℤ] a) = r * χ a := fun r a => by
    simp [χt, Algebra.TensorProduct.productMap_apply_tmul]
  obtain ⟨s, hs⟩ := Module.projective_def'.mp hproj
  have hsx : ∀ x, (s x).sum (fun y c => c • y) = x := by
    intro x
    have := LinearMap.congr_fun hs x
    simpa [Finsupp.linearCombination_apply] using this
  let g : H → C := fun y => Function.surjInv Ideal.Quotient.mk_surjective (l₀ y)
  have hg : ∀ y, Ideal.Quotient.mk I (g y) = l₀ y := fun y =>
    Function.surjInv_eq Ideal.Quotient.mk_surjective (l₀ y)
  let F : H → C := fun x => (s x).sum (fun y c => χt c * g y)
  have hadd : ∀ x x', F (x + x') = F x + F x' := by
    intro x x'
    simp only [F, map_add (f := _)]
    exact Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul])
  have hS : ∀ (t : C ⊗[ℤ] A) x, F (t • x) = χt t * F x := by
    intro t x
    simp only [F, map_smul]
    rw [Finsupp.sum_smul_index (by simp), Finsupp.mul_sum]
    simp [_root_.mul_assoc]
  have hr : ∀ (r : C) (x : H), r • x = ((r ⊗ₜ[ℤ] (1 : A) : C ⊗[ℤ] A) • x) := by
    intro r x
    rw [GlobalTheory.HTSummand.tensorModOf_tmul, map_one]
    rfl
  have ha : ∀ (a : A) (x : H), σ a x = ((1 ⊗ₜ[ℤ] a : C ⊗[ℤ] A) • x) := by
    intro a x
    rw [GlobalTheory.HTSummand.tensorModOf_tmul, one_smul]
  let l : H →ₗ[C] C :=
    { toFun := F
      map_add' := hadd
      map_smul' := by
        intro r x
        show F (r • x) = r * F x
        rw [hr, hS, hχt, map_one, _root_.mul_one] }
  have hl₀t : ∀ (t : C ⊗[ℤ] A) y, l₀ (t • y) = Ideal.Quotient.mk I (χt t) * l₀ y := by
    intro t y
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r a =>
      rw [GlobalTheory.HTSummand.tensorModOf_tmul, l₀.map_smul, hl₀, hχt, map_mul, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, _root_.mul_assoc]
    | add t t' h h' => rw [add_smul, map_add (f := _), h, h', map_add (f := _), map_add (f := _), add_mul]
  refine ⟨l, ?_, ?_⟩
  · intro a x
    show F (σ a x) = χ a * F x
    rw [ha, hS, hχt, _root_.one_mul]
  · intro x
    show Ideal.Quotient.mk I (F x) = l₀ x
    conv_rhs => rw [← hsx x]
    simp only [F, map_finsuppSum, map_mul, hg, hl₀t]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeAutomorphismCongrOneModDetEqOneStatement
section
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_automorphism_congr_one_mod_det_eq_one : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X ≃+ X) (m : ℕ), 3 ≤ m → (∀ x, CongMod m (k x) x) → LinearMap.det (k.toIntLinearEquiv : X →ₗ[ℤ] X) = 1 := by
  first | exact @GlobalTheory.Poinc.det_eq_one_of_congMod | exact GlobalTheory.Poinc.det_eq_one_of_congMod | (intros; apply GlobalTheory.Poinc.det_eq_one_of_congMod <;> assumption)
end

