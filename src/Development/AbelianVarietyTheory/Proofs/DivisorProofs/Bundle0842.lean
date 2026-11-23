module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0802

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValSpMapComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.ExpCoord

theorem val_spMap_comp {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {X : Scheme.{0}} (y : Sp S ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap φ ≫ y) ⁻¹ᵁ U) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of S')).hom.hom (((spMap φ ≫ y).appLE U ⊤ h').hom f) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((y.appLE U ⊤ h).hom f)) := by
  have e : (spMap φ ≫ y).appLE U ⊤ h' = y.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap φ) y U ⊤ ⊤ h le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((y.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  rw [e]
  exact e2

theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom f) := by
  unfold valAt'
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h1 : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dite_eq_left h, dite_eq_left h1]
    unfold valAt
    rw [← Scheme.Hom.appLE_comp_appLE x φ U (φ ⁻¹ᵁ U) ⊤ le_rfl h1]
    rfl
  · have h1 : ¬ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dite_eq_right h, dite_eq_right h1]

theorem deriv_scale {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) {v : Sp (DualNumber ℂ) ⟶ X}
    {w : Fin g → ℂ} (h : IsDerivAt0 e w v) (s : ℂ) : IsDerivAt0 e (s • w) (spMap (epsScaleR s) ≫ v) := by
  have hsub : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := GlobalTheory.UnifDifferential.subsingleton_primeSpectrum ℂ ℂ
  refine ⟨?_, fun U h' f => ?_⟩
  · have hc : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (epsScaleR s) = (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := by
      refine RingHom.ext fun x => ?_
      show (TrivSqZeroExt.map _ x).fst = x.fst
      exact TrivSqZeroExt.fst_map _ _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
    exact h.1
  · have hv : ⊤ ≤ v ⁻¹ᵁ U := by
      intro x _
      have := h' (Set.mem_univ x)
      have hx : (spMap (epsScaleR s)) x = x := Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) _ _
      change v ((spMap (epsScaleR s)) x) ∈ U at this
      rwa [hx] at this
    rw [val_spMap_comp (epsScaleR s) v U hv h' f, map_smul, ← h.2 U hv f]
    simp [epsScaleR]

theorem deriv_comp {g : ℕ} {X Y : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y))
    (φ : X ⟶ Y) (Rho : Matrix (Fin g) (Fin g) ℂ) (hol : IsHolTo Set.univ e') (hc : ∀ z, e' (Rho *ᵥ z) = e z ≫ φ)
    {v : Sp (DualNumber ℂ) ⟶ X} {w : Fin g → ℂ} (h : IsDerivAt0 e w v) : IsDerivAt0 e' (Rho *ᵥ w) (v ≫ φ) := by
  have h0 : e' 0 = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v ≫ φ := by
    rw [← Category.assoc, h.1, ← hc, Matrix.mulVec_zero]
  refine ⟨h0.symm, fun U hU f => ?_⟩
  have h1 : ⊤ ≤ v ⁻¹ᵁ (φ ⁻¹ᵁ U) := hU
  rw [← Scheme.Hom.appLE_comp_appLE v φ U (φ ⁻¹ᵁ U) ⊤ le_rfl h1]
  refine (h.2 (φ ⁻¹ᵁ U) h1 ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom f)).trans ?_
  set G : (Fin g → ℂ) → ℂ := fun z => valAt' (e' z) U f with hG
  have hfun : (fun z => valAt' (e z) (φ ⁻¹ᵁ U) ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom f)) = fun z => G (Rho *ᵥ z) := by
    funext z
    rw [hG]
    dsimp only
    rw [hc, valAt'_comp]
  rw [hfun]
  have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e' b ⁻¹ᵁ U} := by
    refine ⟨Set.mem_univ _, fun x _ => ?_⟩
    rw [h0]
    exact hU (Set.mem_univ _)
  have hd : DifferentiableAt ℂ G 0 :=
    ((hol U f).2 0 hmem).differentiableAt ((hol U f).1.mem_nhds hmem)
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin Rho)
  have hL0 : L 0 = 0 := map_zero L
  have hG' : HasFDerivAt G (fderiv ℂ G 0) (L 0) := by rw [hL0]; exact hd.hasFDerivAt
  have := hG'.comp (0 : Fin g → ℂ) L.hasFDerivAt
  show (fderiv ℂ (G ∘ ⇑L) 0) w = _
  rw [this.fderiv]
  rfl

def toSp {A : Over (Sp ℂ)} (v : epsPt (𝟙 (Sp ℂ)) ⟶ A) : Chart.sp (R₀ := ℂ) (DualNumber ℂ) ⟶ A :=
  Over.homMk v.left (by simpa using Over.w v)

theorem toSp_eq {A : Over (Sp ℂ)} (v : epsPt (𝟙 (Sp ℂ)) ⟶ A) :
    toSp v = (Over.homMk (𝟙 _) (by simp) : Chart.sp (R₀ := ℂ) (DualNumber ℂ) ⟶ epsPt (𝟙 (Sp ℂ))) ≫ v := by
  apply Over.OverMorphism.ext
  simp [toSp]

theorem toSp_mul {A : Over (Sp ℂ)} [GrpObj A] (v v' : epsPt (𝟙 (Sp ℂ)) ⟶ A) :
    toSp (v * v') = toSp v * toSp v' := by
  rw [toSp_eq, toSp_eq, toSp_eq, MonObj.comp_mul]

theorem one_left {A : Over (Sp ℂ)} [GrpObj A] : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ A).left = η[A].left := by
  have h1 : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ A) = toUnit _ ≫ η[A] := rfl
  have h2 : (toUnit (Over.mk (𝟙 (Sp ℂ))) : Over.mk (𝟙 (Sp ℂ)) ⟶ 𝟙_ (Over (Sp ℂ))) = 𝟙 (Over.mk (𝟙 (Sp ℂ))) := toUnit_unique _ _
  rw [h1, h2, Category.id_comp]

theorem pullFn_congr {A : Over (Sp ℂ)} {y y' : Chart.sp (R₀ := ℂ) (DualNumber ℂ) ⟶ A} (e : y = y') (U : A.left.Opens)
    (h : ⊤ ≤ y.left ⁻¹ᵁ U) (h' : ⊤ ≤ y'.left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    GlobalTheory.UnifDifferential.pullFn y U h f = GlobalTheory.UnifDifferential.pullFn y' U h' f := by
  subst e; rfl

theorem deriv_mul {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (he : e 0 = 1) {v v' : epsPt (𝟙 (Sp ℂ)) ⟶ A} {w w' : Fin g → ℂ}
    (h : IsDerivAt0 (fun z => (e z).left) w v.left) (h' : IsDerivAt0 (fun z => (e z).left) w' v'.left) :
    IsDerivAt0 (fun z => (e z).left) (w + w') (v * v').left := by
  have ht : ∀ {x : epsPt (𝟙 (Sp ℂ)) ⟶ A},
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ x.left = (e 0).left → Chart.IsTan (toSp x) := by
    intro x hx
    rw [Chart.isTan_iff]
    show spMap _ ≫ x.left = η[A].left
    rw [hx, he, one_left]
  have hv := ht h.1
  have hv' := ht h'.1
  have hm : Chart.IsTan (toSp (v * v')) := by rw [toSp_mul]; exact Chart.isTan_mul hv hv'
  refine ⟨?_, fun U hU f => ?_⟩
  · have := (Chart.isTan_iff _).1 hm
    show spMap _ ≫ (v * v').left = (e 0).left
    rw [he, one_left]
    exact this
  · have hU' : ⊤ ≤ (toSp v * toSp v').left ⁻¹ᵁ U := by rw [← toSp_mul]; exact hU
    obtain ⟨h₁, h₂, hs⟩ := GlobalTheory.UnifDifferential.snd_pullFn_mul hv hv' U hU'
    show (GlobalTheory.UnifDifferential.pullFn (toSp (v * v')) U hU f).snd = _
    rw [pullFn_congr (toSp_mul v v') U hU hU' f, hs, map_add (f := _)]
    exact congrArg₂ (· + ·) (h.2 U h₁ f) (h'.2 U h₂ f)

theorem expCoord : ∀ (g n : ℕ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (x : Sp ℂ ⟶ Sp ℂ) (T : (Fin n → ℂ) → (epsPtR x ⟶ A)), x = 𝟙 _ → IsExp (𝟙 (Sp ℂ)) e → Function.Injective T → (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : ℂ) c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin n → ℂ), ∀ (u : A ⟶ A), IsMonHom u → ∀ (Mu : Matrix (Fin n) (Fin n) ℂ) (Rho : Matrix (Fin g) (Fin g) ℂ), (∀ c, T c ≫ u = T (Mu *ᵥ c)) → (∀ z, e (Rho *ᵥ z) = e z ≫ u) → ∀ w, L (Rho *ᵥ w) = Mu *ᵥ L w := by
  intro g n A _ _ e x T hx hE hT hR hM hS
  subst hx
  obtain ⟨hadd, -, hhol, hd, hu⟩ := hE
  have he0 : e 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  choose Φ hΦ hΦu using hd
  have tanΦ : ∀ w, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (Φ w).left = (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ A).left := by
    intro w
    rw [(hΦ w).1]
    show (e 0).left = _
    rw [he0]
  choose Ψ hΨ using fun w => (hR (Φ w)).1 (tanΦ w)
  have key : ∀ w c, IsDerivAt0 (fun z => (e z).left) w (T c).left → Ψ w = c := by
    intro w c h
    apply hT
    rw [hΨ w]
    exact (hΦu w (T c) h).symm
  have inj : Function.Injective Ψ := by
    intro w w' h
    have e1 : Φ w = Φ w' := by rw [← hΨ w, ← hΨ w', h]
    have ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (Φ w).left = (e 0).left := (hΦ w).1
    obtain ⟨w'', -, hw''⟩ := hu (Φ w) ht
    have a1 := hw'' w (hΦ w)
    have a2 := hw'' w' (by rw [e1]; exact hΦ w')
    rw [a1, a2]
  have surj : Function.Surjective Ψ := by
    intro c
    have ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (T c).left = (e 0).left := by
      rw [he0]; exact (hR (T c)).2 ⟨c, rfl⟩
    obtain ⟨w, hw, -⟩ := hu (T c) ht
    exact ⟨w, key w c hw⟩
  let Lin : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := Ψ
      map_add' := fun w w' => key (w + w') (Ψ w + Ψ w') (by
        rw [hM, hΨ, hΨ]
        exact deriv_mul e he0 (hΦ w) (hΦ w'))
      map_smul' := fun s w => key (s • w) (s • Ψ w) (by
        rw [hS, hΨ]
        exact deriv_scale _ (hΦ w) s) }
  refine ⟨LinearEquiv.ofBijective Lin ⟨inj, surj⟩, ?_⟩
  intro u _ Mu Rho hTu hRho w
  show Ψ (Rho *ᵥ w) = Mu *ᵥ Ψ w
  apply key
  rw [← hTu, Over.comp_left, hΨ]
  exact deriv_comp _ _ u.left Rho hhol (fun z => by rw [hRho, Over.comp_left]) (hΦ w)

end GlobalTheory.ExpCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalPairPowerSumVanish
section
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData
open scoped Pointwise

noncomputable section
namespace GlobalTheory.CentreCpt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem val_eq_one_of_pow_eq_one (hN : N ≠ 0) {x : ValueGroupWithZero k} (h : x ^ N = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one₀ zero_le' h1 hN).ne
  · exact h1
  · exact absurd h (one_lt_pow₀ h1 hN).ne'

theorem mem_KO_of_mem_center {w : GL (Fin N) k} (hw : w ∈ Subgroup.center (GL (Fin N) k))
    (hv : valuation k (w : Matrix (Fin N) (Fin N) k).det = 1) : w ∈ KO k (Fin N) := by
  rw [GeneralLinearGroup.center_eq_range_scalar] at hw
  obtain ⟨a, rfl⟩ := hw
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [GlobalTheory.SplitFlip.mem_KO_iff]; exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  have hdet : ((GeneralLinearGroup.scalar (Fin N) a : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det =
      (a : k) ^ N := by
    simp [Matrix.det_diagonal]
  rw [hdet, map_pow] at hv
  have ha : valuation k (a : k) = 1 := val_eq_one_of_pow_eq_one hN.ne' hv
  have hai : valuation k ((a⁻¹ : kˣ) : k) = 1 := by simp [ha]
  have ent : ∀ b : kˣ, valuation k (b : k) = 1 → ∀ i j : Fin N,
      ((GeneralLinearGroup.scalar (Fin N) b : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] := by
    intro b hb i j
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact (Valuation.mem_integer_iff _ _).2 hb.le
    · exact zero_mem _
  rw [GlobalTheory.SplitFlip.mem_KO_iff, ← map_inv]
  exact ⟨ent a ha, ent a⁻¹ hai⟩

def vdet (k : Type) [Field k] [ValuativeRel k] (N : ℕ) : GL (Fin N) k →* ValueGroupWithZero k :=
  (valuation k).toMonoidWithZeroHom.toMonoidHom.comp ((Units.coeHom k).comp GeneralLinearGroup.det)

theorem vdet_apply (g : GL (Fin N) k) : vdet k N g = valuation k (g : Matrix (Fin N) (Fin N) k).det := rfl

theorem vdet_eq_one_of_mem_KO {g : GL (Fin N) k} (hg : g ∈ KO k (Fin N)) : vdet k N g = 1 := by
  have hle : ∀ h ∈ KO k (Fin N), vdet k N h ≤ 1 := by
    rintro _ ⟨u, rfl⟩
    rw [vdet_apply]
    change valuation k ((algebraMap 𝒪[k] k).mapMatrix (u : Matrix (Fin N) (Fin N) 𝒪[k])).det ≤ 1
    rw [← RingHom.map_det]
    exact ((Valuation.mem_integer_iff _ _).1 (u.val.det).2)
  have h1 := hle g hg
  have h2 := hle g⁻¹ (inv_mem hg)
  have h3 : vdet k N g * vdet k N g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  refine le_antisymm h1 ?_
  calc (1 : ValueGroupWithZero k) = vdet k N g * vdet k N g⁻¹ := h3.symm
    _ ≤ vdet k N g * 1 := by gcongr
    _ = vdet k N g := mul_one _

theorem exists_compact_center_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (C : Set (GL (Fin N) k)), IsCompact C →
    ∃ D : Set (GL (Fin N) k), IsCompact D ∧ ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ c ∈ C,
      ValuativeRel.valuation k ((z * c : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).det = 1 → z * c ∈ D := by
  intro k _ _ _ _ N C hC
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun c : GL (Fin N) k => c • (KO k (Fin N) : Set (GL (Fin N) k)))
    (fun c => GlobalTheory.SplitFlip.isOpen_KO.smul c)
    (fun c _ => Set.mem_iUnion.2 ⟨c, 1, one_mem _, mul_one c⟩)
  let f : GL (Fin N) k → GL (Fin N) k := fun i =>
    if h : ∃ z ∈ Subgroup.center (GL (Fin N) k), vdet k N (z * i) = 1 then h.choose * i else 1
  refine ⟨⋃ i ∈ t, f i • (KO k (Fin N) : Set (GL (Fin N) k)),
    t.isCompact_biUnion fun i _ => GlobalTheory.SplitFlip.isCompact_KO.smul (f i), ?_⟩
  intro z hz c hc hzc
  rw [← vdet_apply] at hzc
  obtain ⟨i, hi, hci⟩ := Set.mem_iUnion₂.1 (ht hc)
  obtain ⟨κ, hκ, rfl⟩ := hci
  change z * (i * κ) ∈ _
  change vdet k N (z * (i * κ)) = 1 at hzc
  have hvκ := vdet_eq_one_of_mem_KO hκ
  have hzi : vdet k N (z * i) = 1 :=
    calc vdet k N (z * i) = vdet k N (z * i) * vdet k N κ := by rw [hvκ, mul_one]
      _ = 1 := by rw [← map_mul, mul_assoc, hzc]
  have hex : ∃ z ∈ Subgroup.center (GL (Fin N) k), vdet k N (z * i) = 1 := ⟨z, hz, hzi⟩
  have hfi : f i = hex.choose * i := dif_pos hex
  obtain ⟨hzc', hv'⟩ := hex.choose_spec
  set zi := hex.choose
  set w := z * zi⁻¹ with hw
  have hwc : w ∈ Subgroup.center (GL (Fin N) k) := mul_mem hz (inv_mem hzc')
  have hwv : vdet k N w = 1 :=
    calc vdet k N w = vdet k N w * vdet k N (zi * i) := by rw [hv', mul_one]
      _ = vdet k N (z * i) := by rw [← map_mul, ← mul_assoc, hw, inv_mul_cancel_right]
      _ = 1 := hzi
  have hwK : w ∈ KO k (Fin N) := mem_KO_of_mem_center hwc (by rw [← vdet_apply]; exact hwv)
  refine Set.mem_iUnion₂.2 ⟨i, hi, ?_⟩
  rw [hfi]
  refine ⟨w * κ, mul_mem hwK hκ, ?_⟩
  have hz' : z = w * zi := by rw [hw, inv_mul_cancel_right]
  have hcomm := Subgroup.mem_center_iff.1 hwc
  change zi * i * (w * κ) = z * (i * κ)
  rw [hz', ← mul_assoc, hcomm (zi * i)]
  simp only [mul_assoc]

end GlobalTheory.CentreCpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingBirigidifiedTrivialOnAxes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AxisPairing

theorem weilIs_comp_eq_one_of_pull_isGen {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left)
    (hA : IsAbelianScheme A) (hP : P.IsLB) (ψ : A ⟶ G2 A) [IsMonHom ψ]
    (hg : ∃ t : (P.pull ψ.left).Gen, t.IsGen) {n : ℤ} {T : Over S} {u v : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs (G2 A) P n (u ≫ ψ) (v ≫ ψ) c) : c = 1 := by
  have hL : (P.pull ψ.left).IsLB := LB.isLB_pull hP ψ.left
  have h0 : GlobalTheory.CechPic.cls _ hL = 0 := (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 hg
  have hw : LBIso (lbPow (P.pull ψ.left) 1) (P.pull ψ.left) := by
    have hp : (lbPow (P.pull ψ.left) 1).IsLB := LB.isLB_pull hL _
    refine (GlobalTheory.CechPic.cls_eq_iff hp hL).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow hL 1 hp, one_smul]
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds hA hL hP ψ hw h
  rw [Nat.cast_one, _root_.mul_one] at h1
  have iso : LBIso (lbPow (P.pull ψ.left) 0) ((P.pull ψ.left).pull (𝟙 A : A ⟶ A).left) := by
    apply (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_pull hL _)).1
    rw [GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_pull hL,
      Over.id_left, GlobalTheory.CechPic.pull_id, h0, zero_smul]
  have h2 := (GlobalTheory.weilIs_along_hom GlobalTheory.globalFns_holds S A A (𝟙 A)
    (P.pull ψ.left) (P.pull ψ.left) 0 n T u v c c hA hA hL hL inferInstance iso
    (by simpa using h1)).2 h1
  simpa using h2

theorem axes : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), (Out.WeilIs (G2 A) P n (lift u 1) (lift v 1) c → c = 1) ∧ (Out.WeilIs (G2 A) P n (lift 1 u) (lift 1 v) c → c = 1) := by
  intro S A _ _ P hA hP h₂ h₁ n T u v c
  have := GlobalTheory.Raynaud.ProdToric.isMonHom_lift_id_one A A
  have := GlobalTheory.Raynaud.ProdToric.isMonHom_lift_one_id A A
  have e₁ : ∀ w : T ⟶ A, w ≫ lift (𝟙 A) (1 : A ⟶ A) = lift w 1 := fun w => by
    rw [comp_lift, Category.comp_id, MonObj.comp_one]
  have e₂ : ∀ w : T ⟶ A, w ≫ lift (1 : A ⟶ A) (𝟙 A) = lift 1 w := fun w => by
    rw [comp_lift, Category.comp_id, MonObj.comp_one]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← e₁ u, ← e₁ v] at h
    exact weilIs_comp_eq_one_of_pull_isGen P hA hP _ h₁ h
  · rw [← e₂ u, ← e₂ v] at h
    exact weilIs_comp_eq_one_of_pull_isGen P hA hP _ h₂ h

end GlobalTheory.AxisPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftIsOpenImmersionRange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem whiskerLeft_isOpenImmersion_range :
    ∀ (S : Scheme.{0}) (A T Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left →
      IsOpenImmersion (A ◁ z).left ∧ ∀ x, x ∈ Set.range (A ◁ z).left ↔ (snd A T).left x ∈ Set.range z.left := by
  intro S A T Z z hz
  have hc : pullback.snd A.hom Z.hom ≫ z.left = (A ◁ z).left ≫ pullback.snd A.hom T.hom := by
    rw [Over.whiskerLeft_left, pullback.lift_snd]
  have hsq : IsPullback (pullback.snd A.hom Z.hom) (A ◁ z).left z.left (pullback.snd A.hom T.hom) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst A.hom T.hom) (v₂₂ := T.hom) (h₃₁ := A.hom) ?_ hc
      (IsPullback.of_hasPullback A.hom T.hom).flip
    have e1 : (A ◁ z).left ≫ pullback.fst A.hom T.hom = pullback.fst A.hom Z.hom := by
      rw [Over.whiskerLeft_left, pullback.lift_fst, Category.comp_id]
    have e2 : z.left ≫ T.hom = Z.hom := Over.w z
    rw [e1, e2]
    exact (IsPullback.of_hasPullback A.hom Z.hom).flip
  have hsnd : (snd A T).left = pullback.snd A.hom T.hom := by simp
  refine ⟨?_, fun x => ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq hz
  · rw [hsnd]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨pullback.snd A.hom Z.hom y, ?_⟩
      rw [← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]
    · rintro ⟨w, hw⟩
      obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := z.left) (g := pullback.snd A.hom T.hom) w x hw
      refine ⟨hsq.isoPullback.inv p, ?_⟩
      rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_snd, hp2]

end GlobalTheory
end

