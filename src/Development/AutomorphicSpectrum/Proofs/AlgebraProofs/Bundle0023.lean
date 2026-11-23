module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0014
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0010
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeFlagFrame
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagDual

section Linear

variable {O Ω : Type*} [CommRing O] [Field Ω] [Algebra O Ω]
variable {V V₁ : Type*} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁] {N : ℕ}

theorem form_eq_sum {W : Type*} [AddCommGroup W] [Module Ω W] (w : Module.Basis (Fin N) Ω W)
    (φ : W →ₗ[Ω] Ω) (v : W) : φ v = ∑ j, w.repr v j * φ (w j) := by
  conv_lhs => rw [← w.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul]

theorem exists_coeffs (R : Subalgebra O Ω) (L : AddSubgroup V)
    (hst : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (w : Module.Basis (Fin N) Ω V) (m : Fin N → Ω)
    (hg : ∀ i s, (∃ v ∈ L, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = s) ↔ ∃ a ∈ R, s = a * m i)
    (e : Fin N → V) (heL : ∀ i, e i ∈ L) (hez : ∀ i j, i < j → w.repr (e i) j = 0)
    (hed : ∀ i, w.repr (e i) i = m i) (k : ℕ) :
    ∀ v ∈ L, (∀ j : Fin N, k ≤ j.val → w.repr v j = 0) →
      ∃ c : Fin N → Ω, (∀ i, c i ∈ R) ∧ v = ∑ i, c i • e i := by
  induction k with
  | zero =>
    intro v _ hv
    refine ⟨0, fun _ => zero_mem _, ?_⟩
    have : v = 0 := by
      apply w.repr.injective
      ext j
      simpa using hv j (Nat.zero_le _)
    simp [this]
  | succ k ih =>
    intro v hvL hv
    by_cases hk : k < N
    · set i : Fin N := ⟨k, hk⟩ with hi
      obtain ⟨a, haR, ha⟩ := (hg i (w.repr v i)).1
        ⟨v, hvL, fun j hj => hv j (by
          have : i.val < j.val := hj
          simpa [hi] using this), rfl⟩
      have hv' : v - a • e i ∈ L := sub_mem hvL (hst a haR _ (heL i))
      obtain ⟨c, hcR, hc⟩ := ih _ hv' (fun j hj => by
        rcases Nat.lt_or_eq_of_le hj with hlt | heq
        · have hij : i < j := by
            show i.val < j.val
            simpa [hi] using hlt
          have h1 : w.repr v j = 0 := hv j hlt
          simp [h1, hez i j hij]
        · have hij : j = i := Fin.ext (by simp [hi, heq])
          subst hij
          simp [hed, ha])
      refine ⟨fun l => c l + (if l = i then a else 0), fun l => ?_, ?_⟩
      · refine add_mem (hcR l) ?_
        split_ifs
        · exact haR
        · exact zero_mem _
      · have : v = (v - a • e i) + a • e i := by abel
        rw [this, hc]
        simp [add_smul, Finset.sum_add_distrib, ite_smul]
    · exact ih v hvL (fun j _ => hv j (by have := j.isLt; omega))

theorem exists_basis (w : Module.Basis (Fin N) Ω V) (m : Fin N → Ω) (hm : ∀ i, m i ≠ 0)
    (e : Fin N → V) (hez : ∀ i j, i < j → w.repr (e i) j = 0) (hed : ∀ i, w.repr (e i) i = m i) :
    ∃ e' : Module.Basis (Fin N) Ω V, ∀ i, e' i = e i := by
  have hdet : IsUnit (w.det e) := by
    rw [Module.Basis.det_apply, isUnit_iff_ne_zero,
      Matrix.det_of_upperTriangular (M := w.toMatrix e)]
    · refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      simpa [Module.Basis.toMatrix_apply, hed] using hm i
    · intro i j hij
      simpa [Module.Basis.toMatrix_apply] using hez j i hij
  obtain ⟨hli, hsp⟩ := (Module.Basis.is_basis_iff_det w).2 hdet
  exact ⟨Module.Basis.mk hli hsp.ge, fun i => by simp⟩

theorem coord_w (w e' : Module.Basis (Fin N) Ω V) (m : Fin N → Ω) (hm : ∀ i, m i ≠ 0)
    (hez : ∀ i j, i < j → w.repr (e' i) j = 0) (hed : ∀ i, w.repr (e' i) i = m i) (r : Fin N) :
    (∀ l, l < r → e'.repr (w l) r = 0) ∧ e'.repr (w r) r = (m r)⁻¹ := by
  have hexp : ∀ l, (∀ j, j < l → e'.repr (w j) r = 0) →
      e'.repr (e' l) r = m l * e'.repr (w l) r := by
    intro l hl
    have h0 : e'.repr (e' l) r = ∑ j, w.repr (e' l) j * e'.repr (w j) r :=
      form_eq_sum w (e'.coord r) (e' l)
    rw [h0, Finset.sum_eq_single l]
    · rw [hed]
    · intro j _ hjl
      rcases lt_or_gt_of_ne hjl with h | h
      · simp [hl j h]
      · simp [hez l j h]
    · simp
  have hlow : ∀ n : ℕ, ∀ l : Fin N, l.val = n → l < r → e'.repr (w l) r = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro l hln hlr
      have h1 := hexp l (fun j hj => ih j.val (by rw [← hln]; exact hj) j rfl (hj.trans hlr))
      have h2 : e'.repr (e' l) r = 0 := by
        simp [Module.Basis.repr_self, Finsupp.single_apply, hlr.ne]
      rw [h2] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left (hm l)
  have hlow' : ∀ l, l < r → e'.repr (w l) r = 0 := fun l hl => hlow _ l rfl hl
  refine ⟨hlow', ?_⟩
  have h1 := hexp r hlow'
  have h2 : e'.repr (e' r) r = 1 := by simp
  rw [h2] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem dual_graded (R : Subalgebra O Ω) (L : AddSubgroup V) (L₁ : AddSubgroup V₁)
    (hst : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (w : Module.Basis (Fin N) Ω V) (m : Fin N → Ω)
    (hm : ∀ i, m i ≠ 0)
    (hg : ∀ i s, (∃ v ∈ L, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = s) ↔ ∃ a ∈ R, s = a * m i)
    (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (hβ : Function.Surjective β.flip)
    (hL₁ : ∀ u, u ∈ L₁ ↔ ∀ v ∈ L, β v u ∈ R) (w₁ : Module.Basis (Fin N) Ω V₁)
    (hw : ∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) (j : Fin N) (s : Ω) :
    (∃ u ∈ L₁, (∀ l, j < l → w₁.repr u l = 0) ∧ w₁.repr u j = s) ↔
      ∃ a ∈ R, s = a * (m j.rev)⁻¹ := by
  have hcoord : ∀ u l, w₁.repr u l = β (w l.rev) u := by
    intro u l
    rw [form_eq_sum w₁ (β (w l.rev)) u]
    simp [hw, Fin.rev_inj]
  have hex : ∀ i, ∃ v, v ∈ L ∧ (∀ l, i < l → w.repr v l = 0) ∧ w.repr v i = m i := by
    intro i
    obtain ⟨v, hv, h1, h2⟩ := (hg i (m i)).2 ⟨1, one_mem _, by simp⟩
    exact ⟨v, hv, h1, h2⟩
  choose e heL hez hed using hex
  obtain ⟨e', he'⟩ := exists_basis w m hm e hez hed
  have hez' : ∀ i l, i < l → w.repr (e' i) l = 0 := fun i l h => by rw [he']; exact hez i l h
  have hed' : ∀ i, w.repr (e' i) i = m i := fun i => by rw [he']; exact hed i
  set r := j.rev with hr
  obtain ⟨hlow, htop⟩ := coord_w w e' m hm hez' hed' r
  constructor
  · rintro ⟨u, hu, hz, rfl⟩
    refine ⟨m r * w₁.repr u j, ?_, ?_⟩
    · have hmem := (hL₁ u).1 hu _ (heL r)
      have hsum : β (e r) u = m r * w₁.repr u j := by
        have h0 : β (e r) u = ∑ l, w.repr (e r) l * β (w l) u :=
          form_eq_sum w (β.flip u) (e r)
        rw [h0, Finset.sum_eq_single r]
        · rw [hed, hcoord u j]
        · intro l _ hlr
          rcases lt_or_gt_of_ne hlr with h | h
          · have hl : j < l.rev := by
              rw [hr] at h
              have := Fin.rev_lt_rev.2 h
              simpa using this
            have h2 := hcoord u l.rev
            rw [Fin.rev_rev] at h2
            rw [← h2, hz _ hl, mul_zero]
          · simp [hez r l h]
        · simp
      rwa [hsum] at hmem
    · field_simp [hm r]
  · rintro ⟨a, haR, rfl⟩
    obtain ⟨u, hu⟩ := hβ (a • e'.coord r)
    have hβu : ∀ v, β v u = a * e'.repr v r := fun v => by
      have := LinearMap.congr_fun hu v
      simpa using this
    refine ⟨u, (hL₁ u).2 fun v hv => ?_, fun l hl => ?_, ?_⟩
    · obtain ⟨c, hcR, hc⟩ := exists_coeffs R L hst w m hg e heL hez hed N v hv
        (fun l hl => by have := l.isLt; omega)
      have hcoef : e'.repr v r = c r := by
        have : v = ∑ i, c i • e' i := by simpa [he'] using hc
        rw [this]
        set_option synthInstance.maxHeartbeats 100000 in
          simp [map_sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
      rw [hβu, hcoef]
      exact mul_mem haR (hcR r)
    · rw [hcoord, hβu, hlow _ (by simpa [hr] using Fin.rev_lt_rev.2 hl), mul_zero]
    · rw [hcoord, hβu, ← hr, htop]

end Linear

theorem main : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), IsDualLat O x β E.lat F.lat → ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → ∀ w₁ : Module.Basis (Fin N) Ω V₁, (∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) → IsFlagFrame x F w₁ (fun j => -b j.rev) := by
  intro O _ Ω _ _ K _ _ ι _ x N V _ _ V₁ _ _ E F β hdual w b hE w₁ hw
  refine ⟨fun c hc i => ?_⟩
  have hc' : mseg x c ≠ 0 := hc
  have hx : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc' k (Finset.mem_univ k)
  have hm : ∀ l, (∏ k, x ⟨k, c k⟩ ^ b l k) ≠ 0 := fun l =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  ext s
  have key := dual_graded (chartRing O (mseg x) c) (E.lat c) (F.lat c)
    (fun a ha v hv => E.stable c a ha v hv) w (fun l => ∏ k, x ⟨k, c k⟩ ^ b l k) hm
    (fun l s => by
      have := Set.ext_iff.1 (hE.graded c hc l) s
      exact this)
    β hdual.1.2 (hdual.2 c hc') w₁ hw i s
  have hinv : (∏ k, x ⟨k, c k⟩ ^ b i.rev k)⁻¹ = ∏ k, x ⟨k, c k⟩ ^ (-b i.rev) k := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun k _ => by simp [zpow_neg]
  rw [hinv] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.Num.FlagDual
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FilteredExactSequenceProjectorBundles
section
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

theorem subDeg_range_shortExact : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (P : V →ₗ[K] V) (P' : V' →ₗ[K] V') (P'' : V'' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → (∀ x, P (P x) = P x) → (∀ x, P' (P' x) = P' x) → (∀ x, P'' (P'' x) = P'' x) → (∀ x, f (P x) = P' (f x)) → (∀ y, g (P' y) = P'' (g y)) → IsHom C L' L' P' → subDeg C L' (LinearMap.range P') = subDeg C L (LinearMap.range P) + subDeg C L'' (LinearMap.range P'') := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g P P' P'' hB hSE hP hP' hP'' hfP hgP hHom
  obtain ⟨hinj, hex, hsurj, hL, hL''⟩ := hSE
  have mP : ∀ v ∈ LinearMap.range P, P v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP u
  have mP' : ∀ v ∈ LinearMap.range P', P' v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP' u
  have mP'' : ∀ v ∈ LinearMap.range P'', P'' v = v := by
    intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    exact hP'' u
  let f₀ : LinearMap.range P →ₗ[K] LinearMap.range P' :=
    LinearMap.codRestrict (LinearMap.range P') (f.domRestrict (LinearMap.range P)) (fun v =>
      LinearMap.mem_range.2 ⟨f v, by
        show P' (f v) = f v
        rw [← hfP, mP _ v.2]⟩)
  let g₀ : LinearMap.range P' →ₗ[K] LinearMap.range P'' :=
    LinearMap.codRestrict (LinearMap.range P'') (g.domRestrict (LinearMap.range P')) (fun v =>
      LinearMap.mem_range.2 ⟨g v, by
        show P'' (g v) = g v
        rw [← hgP, mP' _ v.2]⟩)
  have hSE0 : ShortExact C (sub C L (LinearMap.range P)) (sub C L' (LinearMap.range P'))
      (sub C L'' (LinearMap.range P'')) f₀ g₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x y h
      apply Subtype.ext
      apply hinj
      exact congrArg Subtype.val h
    · intro y
      constructor
      · intro hy
        have hy' : g (y : V') = 0 := congrArg Subtype.val hy
        obtain ⟨x, hx⟩ := (hex (y : V')).1 hy'
        refine ⟨⟨P x, LinearMap.mem_range_self P x⟩, ?_⟩
        apply Subtype.ext
        show f (P x) = (y : V')
        rw [hfP, hx, mP' _ y.2]
      · rintro ⟨x, rfl⟩
        apply Subtype.ext
        show g (f (x : V)) = 0
        exact (hex _).2 ⟨x, rfl⟩
    · intro z
      obtain ⟨y, hy⟩ := hsurj (z : V'')
      refine ⟨⟨P' y, LinearMap.mem_range_self P' y⟩, ?_⟩
      apply Subtype.ext
      show g (P' y) = (z : V'')
      rw [hgP, hy, mP'' _ z.2]
    · intro i x
      show (x : V) ∈ L i ↔ f (x : V) ∈ L' i
      exact hL i x
    · intro i z
      constructor
      · intro hz
        obtain ⟨y, hyL, hy⟩ := (hL'' i z).1 hz
        refine ⟨⟨P' y, LinearMap.mem_range_self P' y⟩, hHom i y hyL, ?_⟩
        apply Subtype.ext
        show g (P' y) = (z : V'')
        rw [hgP, hy, mP'' _ z.2]
      · rintro ⟨y, hyL, rfl⟩
        exact (hL'' i _).2 ⟨y, hyL, rfl⟩
  have hBW : IsBun C (sub C L' (LinearMap.range P')) :=
    (SubQuot.isBun_sub_quot K C V' L' (LinearMap.range P') hB).1
  exact (deg_shortExact K C (LinearMap.range P) (LinearMap.range P') (LinearMap.range P'')
    (sub C L (LinearMap.range P)) (sub C L' (LinearMap.range P')) (sub C L'' (LinearMap.range P''))
    f₀ g₀ hBW hSE0).2.2

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatSubgroupSchemeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
open GlobalTheory.CompanionTheory.Ar.GR.SubGrp (exists_eq_spMap exists_sp_iso exists_grpObj_of_mono) in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_subgroup_scheme :
    ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A]
      (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A),
      IsFinFlatSub A B h → ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by
  intro R _ A _ B _ _ h H
  have hmono : Mono h := by
    constructor
    intro T a b hab
    apply Over.OverMorphism.ext
    refine T.left.affineCover.hom_ext _ _ fun k => ?_
    let T' : Over (Spec (CommRingCat.of R)) := Over.mk (T.left.affineCover.f k ≫ T.hom)
    let j : T' ⟶ T := Over.homMk (T.left.affineCover.f k) rfl
    have : IsAffine T'.left := inferInstanceAs (IsAffine (T.left.affineCover.X k))
    obtain ⟨S, _, _, i, _⟩ := exists_sp_iso T'
    obtain ⟨φ, hφ⟩ := exists_eq_spMap (i ≫ j ≫ a)
    obtain ⟨ψ, hψ⟩ := exists_eq_spMap (i ≫ j ≫ b)
    have hφψ := H.mono S φ ψ (by simp only [← hφ, ← hψ, Category.assoc, hab])
    have hj : j ≫ a = j ≫ b := by rw [← cancel_epi i, hφ, hψ, hφψ]
    exact congrArg (·.left) hj
  have hmul : ∃ m : sp (R₀ := R) B ⊗ sp (R₀ := R) B ⟶ sp (R₀ := R) B,
      m ≫ h = (fst _ _ ≫ h) * (snd _ _ ≫ h) := by
    have : IsAffine (sp (R₀ := R) B).left := inferInstanceAs (IsAffine (Spec _))
    have : IsAffine (sp (R₀ := R) B ⊗ sp (R₀ := R) B).left :=
      Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
        (sp (R₀ := R) B).hom (sp (R₀ := R) B).hom
    obtain ⟨S, _, _, j, _⟩ := exists_sp_iso (sp (R₀ := R) B ⊗ sp (R₀ := R) B)
    obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ fst _ _)
    obtain ⟨ψ, hψ⟩ := exists_eq_spMap (j ≫ snd _ _)
    obtain ⟨χ, hχ⟩ := H.mul S φ ψ
    refine ⟨inv j ≫ spMap χ, ?_⟩
    rw [Category.assoc, hχ, ← hφ, ← hψ, MonObj.comp_mul, Category.assoc, Category.assoc,
      IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]
  have hone : ∃ e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ sp (R₀ := R) B, e ≫ h = 1 := by
    have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
      inferInstanceAs (IsAffine (Spec _))
    obtain ⟨S, _, _, j, _⟩ := exists_sp_iso (𝟙_ (Over (Spec (CommRingCat.of R))))
    obtain ⟨χ, hχ⟩ := H.one S
    exact ⟨inv j ≫ spMap χ, by rw [Category.assoc, hχ, MonObj.comp_one]⟩
  obtain ⟨i, hi⟩ := H.inv B (AlgHom.id R B)
  have hid : spMap (AlgHom.id R B) = 𝟙 (sp (R₀ := R) B) := by
    apply Over.OverMorphism.ext
    rw [ReciprocityTheory.ChartRestriction.G.Chart.spMap_left, Over.id_left]
    exact Spec.map_id _
  rw [hid, Category.id_comp] at hi
  obtain ⟨m, hm⟩ := hmul
  obtain ⟨e, he⟩ := hone
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono h m e (spMap i) hm he hi
  exact ⟨G, hG, hmono⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeAnnihilatorLatticeHolds
section
namespace GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_stdLat_iff_algebra (R : Subalgebra o Ω) {ι : Type} (v : ι → Ω) :
    v ∈ stdLat R ι ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem linMap_mem_stdLat {F : Type} [Zero F] [Fintype F] {n : ℕ} (R : Subalgebra o Ω) (χ : F → Ω)
    (hχ : ∀ a, χ a ∈ R) (v : Fin n → Ω) (hv : v ∈ stdLat R (Fin n)) :
    linMap n χ v ∈ stdLat R (Fin n → F) := by
  rw [mem_stdLat_iff_algebra] at hv ⊢
  intro x
  simp only [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hv i) (hχ _)

theorem hodge_annihilator_lattice {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F]
    [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω)
    (p : ℕ) (w : Ω) (χ : Sg → F → Ω) (hC : CharData R p w χ) (hB : D.Base R p w) (hp : p.Prime)
    (hN : IsNoetherianRing R) (hF : IsFractionRing R Ω) (hI : IsIntegrallyClosedIn R Ω)
    (φ : Equiv.Perm Sg) (hT : D.TestFacts R p w χ φ) (hG : D.Good₁ R p χ) (τ : Sg) :
    mulLat w (stdLat R _) ≤ D.af R p (χ τ) := by
  have H := _root_.GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main D R p w χ hC hB hG
  obtain ⟨hp0, hwR, -, -, hχ⟩ := hC
  intro x hx
  obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.mp hx
  have hu' : ∀ i, u i ∈ R := (mem_stdLat_iff_algebra R u).mp hu
  refine _root_.GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main R p hp hp0 hN hF hI n (D.af R p (χ τ)) (H.1 τ).1 _ ⟨1, ?_⟩ ?_
  · have hy : linMap n (χ τ) (w • u) ∈ stdLat R (Fin n → F) :=
      linMap_mem_stdLat R (χ τ) (hχ τ).2.2 _ ((mem_stdLat_iff_algebra R _).mpr fun i => by
        simpa using R.mul_mem hwR (hu' i))
    rw [LieLatticeData.af, AddSubgroup.mem_comap]
    refine AddSubgroup.mem_sup_right (AddSubgroup.mem_map.mpr ⟨_, hy, ?_⟩)
    simp [map_smul]
  · intro C _ _ _ _ RC hTP
    have hRC : ∀ a ∈ R, algebraMap Ω C a ∈ RC := hTP.2.2.2
    rw [← ((H.2 C RC hRC).2 τ).1]
    have hFa := hT C RC hTP
    refine hFa.le_af τ (AddSubgroup.mem_map.mpr ⟨bcMap Ω C (Fin n) u, ?_, ?_⟩)
    · exact (mem_stdLat_iff_algebra RC _).mpr fun i => by simpa [bcMap] using hRC _ (hu' i)
    · ext i
      simp [bcMap]

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateLatticeBaseChangePairing
section
open GlobalTheory.CompanionTheory.Ar.HT NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem htChart_of_projective_module : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p R N : ℕ) (W Ω : Type) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Projective A W] [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (j : W →ₗ[A] Ω), IsBaseChange K j → ∀ (ρ : 𝓞 E →+* Module.End A W) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)) (h : (Fin N → 𝓞 E) →+ W), (∀ x, e x x = 0) → (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y)) → (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → (∀ (a : 𝓞 E) x, ∃ y, h (a • x) = ρ a (h x) + (p ^ R) • y) → ∃ D : HTChart A K c p R N Ω, D.om = LinearMap.range j ∧ D.e = e ∧ (∀ x, D.h x = j (h x)) ∧ ∀ a w, D.ρΩ a (j w) = j (ρ a w) :=
  @PositivityTheory.HtPt.Htat.chart_build

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsAddCharactersStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_contains_add_characters : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ ψ : AddChar N C, (fun x => ψ x) ∈ AA.carrier := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.addChar_mem_hopfOrder | exact GlobalTheory.CompanionTheory.Ar.GR.addChar_mem_hopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.addChar_mem_hopfOrder <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderPullbackAlongHom
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_order_pullback_along_hom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (A' : HopfOrder (C := C) R N') (j : N →+ N'), (∀ g ∈ A'.carrier, (fun x => g (j x)) ∈ AA.carrier) → (∀ g ∈ AA.carrier, (∀ k ∈ j.ker, g k = 0) → g ∈ (augIdeal A'.carrier).map (LinearMap.funLeft R C (j : N → N')) * AA.carrier) → A'.carrier.map (LinearMap.funLeft R C (j : N → N')) = invFun AA.carrier j.ker := by
  first | exact @PositivityTheory.HtPt.Rh.sub_closed | exact PositivityTheory.HtPt.Rh.sub_closed
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeLengthMonoStrict
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem submodule_eq_of_hasLen_eq : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (ι : Type) [Fintype ι] (L L' : Submodule R (ι → R)), L ≤ L' → ∀ x y : NNReal, x ≠ 0 → HasLen v R ((ι → R) ⧸ L) x → HasLen v R ((ι → R) ⧸ L') y → x ≤ y ∧ (x = y → L = L') :=
  @PositivityTheory.HtPt.Rh.len_eq

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PtAfTypeMain
section
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem pt_af_type_main : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (MM : Submodule RC ((I → ZMod p) → C)), MM ≤ intFun RC _ → ∀ {F : Type} [Field F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (χ : F → RC), χ 0 = 0 → χ 1 = 1 → ∀ (i : (Fin n → F) →+ (I → ZMod p)) (π : (I → ZMod p) →+ (Fin n → F)), (∀ y, π (i y) = y) → (∀ h ∈ MM, (fun x => h (i (π x))) ∈ MM) → (MM.map (LinearMap.funLeft RC C (i : (Fin n → F) → (I → ZMod p)))).toAddSubgroup = D.M → ∀ (Pm : Matrix (Fin n) I RC) (J : Matrix I (Fin n) RC), Pm * J = 1 → (∀ (k : Fin n) (x : I → ZMod p), (∑ j, Pm k j * ((x j).val : RC)) - χ (π x k) ∈ Ideal.span {(p : RC)}) → (∀ l ∈ afLat p MM, Matrix.vecMul l (J * Pm) ∈ afLat p MM) → (∀ l : Fin n → RC, (fun k => (l k : C)) ∈ D.af RC p (fun a => (χ a : C)) ↔ Matrix.vecMul l Pm ∈ afLat p MM) ∧ ∀ u : Fin n → C, u ∈ D.hh RC p (fun a => (χ a : C)) ↔ ∀ l ∈ afLat p MM, (∑ j, (l j : C) * (J.map (algebraMap RC C)).mulVec u j) ∈ RC :=
  @PositivityTheory.Xgn.t_pt_af_type

end GlobalTheory.CompanionTheory.Ar.Num
end

