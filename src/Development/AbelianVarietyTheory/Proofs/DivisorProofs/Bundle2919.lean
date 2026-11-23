module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInverseNatCast
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldOfTangentVectorOrigin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisPermutesWeightPartsUpToRoots
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GalPart

open GlobalTheory.UPoinc.USum

section General

open MonObj

variable {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
  {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {lab : S.Gam → S'.Gam} {φ : Ω →+* Ω'}
  {P₀ : PolAV (Sp Ω')} {a : P₀.A.left ⟶ ρ.P.A.left} {a' : P₀.A.left ⟶ ρ'.P.A.left}

theorem exists_isGenLab_of (h₁ : IsGrpPullback P₀.A ρ.P.A (spMap (φ.comp S.R.val.toRingHom)) a)
    (h₂ : IsGrpPullback P₀.A ρ'.P.A (spMap S'.R.val.toRingHom) a') (l₁ : LBIso P₀.L (ρ.P.L.pull a))
    (l₂ : LBIso P₀.L (ρ'.P.L.pull a'))
    (hpt : ∀ x, ∃ w : Sp Ω' ⟶ P₀.A.left, w ≫ a = spMap (φ.comp S.R.val.toRingHom) ≫ (ρ.pt x).left ∧
      w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (lab x)).left) :
    ∃ x, IsGenLab ρ ρ' lab φ P₀ a a' x ∧ ∀ b b', x (b + b') = x b * x b' := by
  obtain ⟨w, hw, hadd, -⟩ := GalAct.exists_generic_labels ρ' h₂
  obtain ⟨e, he⟩ := GalAct.exists_mulEquiv_points h₁ (𝟙 _) _ (Category.id_comp _)
  have := GalTrans.mono_val S'.R S'.frac
  have : Mono a' := (MorphismProperty.monomorphisms Scheme).of_isPullback h₂.1.flip (.infer_property _)
  refine ⟨fun b => e (w b), ⟨h₁, h₂, l₁, l₂, fun b => ⟨(w b).left, Over.w (w b), (he _).symm, hw b⟩,
    fun k => ?_⟩, fun b b' => by simp only [hadd, map_mul]⟩
  obtain ⟨v, hv, hv'⟩ := hpt k
  obtain rfl : v = (w (lab k)).left := (cancel_mono a').1 (hv'.trans (hw _).symm)
  exact Over.OverMorphism.ext ((he _).trans hv)

variable {x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)}

theorem exists_conj_over (hx : IsGenLab ρ ρ' lab φ P₀ a a' x) (σ : Ω' →+* Ω') (hσ : Function.Surjective σ)
    (hφ : σ.comp φ = φ) : ∃ (g : S'.Gam ≃+ S'.Gam)
      (s : genPt (φ.comp S.R.val.toRingHom) ⟶ genPt (φ.comp S.R.val.toRingHom)) (t : P₀.A.left ⟶ P₀.A.left),
      s.left = spMap σ ∧ (∀ b, x (g b) = s ≫ x b) ∧ (∀ k, g (lab k) = lab k) ∧ t ≫ a = a ∧
      IsGrpPullback P₀.A P₀.A (spMap σ) t ∧ LBIso P₀.L (P₀.L.pull t) ∧
      ∀ y (w w' : Sp Ω' ⟶ P₀.A.left), w ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt y).left →
        w' ≫ t = spMap σ ≫ w → w' ≫ a' = spMap S'.R.val.toRingHom ≫ (ρ'.pt (g y)).left := by
  obtain ⟨h₁, h₂, l₁, l₂, hw, hlab⟩ := hx
  have hs : spMap σ ≫ spMap (φ.comp S.R.val.toRingHom) = spMap (φ.comp S.R.val.toRingHom) :=
    GalTrans.sp_comp (by rw [← RingHom.comp_assoc, hφ])
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : P₀.A.left ⟶ P₀.A.left, t ≫ a = a ∧ t ≫ P₀.A.hom = P₀.A.hom ≫ spMap σ :=
    ⟨h₁.1.lift a (P₀.A.hom ≫ spMap σ) (by rw [Category.assoc, hs, h₁.1.w]), h₁.1.lift_fst _ _ _, h₁.1.lift_snd _ _ _⟩
  have ht : IsGrpPullback P₀.A P₀.A (spMap σ) t := h₁.cancel (h₁.congr hs.symm ht₁.symm) ht₂
  have lt : LBIso (P₀.L.pull t) (ρ.P.L.pull a) :=
    l₁.chartPull (Geo.Tor.chartPullPull P₀.L t t rfl)
      (chartPullSame ρ.P.L (fun _ => a) (fun _ => a) _ t fun _ => ht₁.symm)
  obtain ⟨g, hg, hg'⟩ := GalAct.exists_label_action ρ' h₂ σ hσ ht
  have := GalTrans.mono_val S'.R S'.frac
  have : Mono a' := (MorphismProperty.monomorphisms Scheme).of_isPullback h₂.1.flip (.infer_property _)
  refine ⟨g, Over.homMk (spMap σ) hs, t, rfl, fun b => Over.OverMorphism.ext ?_, fun k => ?_, ht₁, ht,
    LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB _) (pull_isLB P₀.isLB _) l₁ lt.symm, hg⟩
  · obtain ⟨w, e₀, e₁, e₂⟩ := hw b
    obtain ⟨w', -, e₁', e₂'⟩ := hw (g b)
    have c : (spMap σ ≫ w) ≫ P₀.A.hom = 𝟙 _ ≫ spMap σ := by rw [Category.assoc, e₀]; simp
    have k := ht.1.lift_fst _ _ c
    obtain rfl : w' = ht.1.lift _ _ c := (cancel_mono a').1 (e₂'.trans (hg b w _ e₂ k).symm)
    rw [← e₁', ← ht₁, reassoc_of% k, e₁]
    rfl
  · obtain ⟨w, e₀, e₁, e₂⟩ := hw (lab k)
    refine hg' _ w e₂ (h₁.1.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc, ht₁, e₁, hlab]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hs)).symm
    · rw [Category.assoc, Category.assoc, ht₂, reassoc_of% e₀, e₀, Category.comp_id]


open Classical in
theorem exists_root_conj [ArithBase o Ω] [ArithBase o' Ω'] (hx : IsGenLab ρ ρ' lab φ P₀ a a' x)
    (hadd : ∀ b b', x (b + b') = x b * x b') {m : ℕ} (hm : S'.N = m ^ 2) (H : AddSubgroup S'.Gam) (x₀ : S.Gam)
    (h₀ : S.th x₀ ≠ 0) (h₀' : S'.th (lab x₀) ≠ 0) {κ : S.Gam} {h : S'.Gam} (hh : h ∈ H) (e : m • h = lab κ) :
    ∃ ξ : Ω', (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ (σ : Ω' →+* Ω'), σ.comp φ = φ →
      ∀ (s : genPt (φ.comp S.R.val.toRingHom) ⟶ genPt (φ.comp S.R.val.toRingHom)), s.left = spMap σ →
      ∀ g : S'.Gam ≃+ S'.Gam, (∀ b, x (g b) = s ≫ x b) → (∀ k, g (lab k) = lab k) → (∀ y, g y ∈ H ↔ y ∈ H) →
      ∀ b, σ (ξ * (partV S' H ρ'.i₀ b h / S'.th (lab x₀))) = ξ * (partV S' H ρ'.i₀ (g b) h / S'.th (lab x₀)) := by
  have := Fintype.ofFinite (S'.perp H)
  choose V hV₁ using fun t : S'.perp H => TV.ex hx hadd hm t e
  have hV : ∀ h' ∈ H, m • h' = lab κ → ∀ t : S'.perp H, TV ρ x m t h' κ (V t) := fun h' hh' e' t => by
    have := (hV₁ t).transl hx hadd hm (k := h' - h) (by rw [smul_sub, e, e', sub_self]) (t.2 _ (sub_mem hh' hh))
    rwa [add_sub_cancel] at this
  have hφ₀ : φ (S.th x₀) ≠ 0 := (map_ne_zero φ).2 h₀
  obtain ⟨ξ, hξ, hc⟩ := _root_.GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul ρ ρ' lab φ P₀ a a' x hx m hm κ x₀ h e
  have hf : ∀ b, ξ * (partV S' H ρ'.i₀ b h / S'.th (lab x₀)) =
      algebraMap o' Ω' (Ring.inverse (Nat.card (S'.perp H) : o')) *
        (∑ t : S'.perp H, algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ b t)).val) * V t) / φ (S.th x₀) := fun b => by
    have hv : ∀ t : S'.perp H, V t =
        (ξ * φ (S.th x₀) / S'.th (lab x₀)) * ∑ j, algebraMap o' Ω' (S'.ρ t j ρ'.i₀) * S'.ev h j := fun t => by
      rw [div_mul_eq_mul_div, eq_div_iff h₀']
      exact hc t _ (hV₁ t)
    simp only [hv, partV_eq, mul_left_comm _ (ξ * φ (S.th x₀) / S'.th (lab x₀)), ← Finset.mul_sum]
    field_simp
  refine ⟨ξ, hξ, fun σ hφ s hs g hg hl hH b => ?_⟩
  have hw := hx.weil_conj σ s hs hg
  have h0 : ∀ y y', eStd S'.g _ y y' = 0 ↔ eStd S'.g _ (g y) (g y') = 0 := fun y y' => by
    rw [← zeta_pow_eq_one_iff, ← zeta_pow_eq_one_iff, ← hw, map_eq_one_iff σ σ.injective]
  have hT : ∀ t, t ∈ S'.perp H ↔ g t ∈ S'.perp H := fun t =>
    ⟨fun ht y hy => by
      obtain ⟨y, rfl⟩ := g.surjective y
      exact (h0 _ _).1 (ht y ((hH y).1 hy)), fun ht y hy => (h0 _ _).2 (ht _ ((hH y).2 hy))⟩
  let e' : S'.perp H ≃ S'.perp H := g.toEquiv.subtypeEquiv hT
  have hζ : ∀ t : S'.perp H, σ (algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ b t)).val)) =
      algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ (g b) (e' t))).val) := fun t => by
    have e₁ : σ (algebraMap o' Ω' (S'.ζN ^ (wtChar S' _ b t).val)) =
        algebraMap o' Ω' (S'.ζN ^ (wtChar S' _ (g b) (e' t)).val) := by
      refine (congrArg (fun q => σ (algebraMap o' Ω' q)) (zetaN_pow_cast _)).trans
        (Eq.trans ?_ (congrArg (algebraMap o' Ω') (zetaN_pow_cast _)).symm)
      rw [map_pow, map_pow, hw, ← map_pow]
      rfl
    have e₂ := congrArg (fun q => σ (algebraMap o' Ω' q)) (zetaN_neg_mul (wtChar S' _ b t))
    have e₃ := congrArg (algebraMap o' Ω') (zetaN_neg_mul (wtChar S' _ (g b) (e' t)))
    simp only [map_mul, map_one] at e₂ e₃
    rw [e₁] at e₂
    exact (eq_inv_of_mul_eq_one_left e₂).trans (eq_inv_of_mul_eq_one_left e₃).symm
  have hσV : ∀ t : S'.perp H, σ (V t) = V (e' t) := fun t =>
    ((hV₁ t).conj σ s hs g.toAddMonoidHom hg).unique ρ'
      (hV (g h) ((hH h).2 hh) (by rw [← map_nsmul, e, hl]) (e' t))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, hf, map_div₀, map_mul, map_inverse_natCast, map_sum,
    show σ (φ (S.th x₀)) = φ (S.th x₀) from RingHom.congr_fun hφ _,
    ← Equiv.sum_comp e' fun t => algebraMap o' Ω' (S'.ζN ^ (-(wtChar S' _ (g b) t)).val) * V t]
  simp only [map_mul, hζ, hσV]

end General

theorem exists_root_galois : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁, ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ (∀ x, a (D.lab x) = D.lab x) ∧ ((∀ x, a x ∈ D.X.S.HH D.X.M z₂ ↔ x ∈ D.X.S.HH D.X.M z₂) → ∀ b κ, σ (U κ * GSum.part D z₁ z₂ b κ) = U κ * GSum.part D z₁ z₂ (a b) κ) := by
  intro g n F W Z i X₁ hg hn hodd hi hE hT hP ε₁ hε₁ D z₁ z₂ hq
  obtain ⟨P₀, a₁, a₂, ε₀, h₁, h₂, l₁, l₂, hε, hpt⟩ := D.same
  obtain ⟨x, hx, hadd⟩ := exists_isGenLab_of h₁ h₂ l₁ l₂ hpt
  have hb : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁ := by
    have hne : (X₁.S.supI X₁.M z₁).Nonempty := X₁.div z₁
    rw [GSum.base, dite_eq_left hne]
    exact hne.some_mem
  have hb' := _root_.GlobalTheory.Poinc.DivDeep.main g n F W Z i X₁ hg hn hodd hi hE hT hP ε₁ hε₁ D z₁ _ hb z₂ hq
  have hl : ∀ κ : X₁.S.Gam, GSum.lift D z₂ κ ∈ D.X.S.HH D.X.M z₂ ∧ ∃ κ', D.m • GSum.lift D z₂ κ = D.lab κ' := fun κ => by
    by_cases h : ∃ h' ∈ D.X.S.HH D.X.M z₂, D.m • h' = D.lab κ
    · rw [GSum.lift, dite_eq_left h]
      exact ⟨h.choose_spec.1, κ, h.choose_spec.2⟩
    · rw [GSum.lift, dite_eq_right h]
      exact ⟨zero_mem _, 0, by rw [smul_zero, map_zero]⟩
  choose U hU hσU using fun κ : X₁.S.HH X₁.M z₁ =>
    exists_root_conj hx hadd D.sq (D.X.S.HH D.X.M z₂) _ hb.1 hb'.1 (hl κ).1 (hl κ).2.choose_spec
  refine ⟨U, hU, fun σ => ?_⟩
  have hφ : (σ : D.X.Ω₁ →+* D.X.Ω₁).comp (algebraMap X₁.Ω₁ D.X.Ω₁) = algebraMap X₁.Ω₁ D.X.Ω₁ :=
    RingHom.ext fun y => σ.commutes y
  obtain ⟨a, s, t, hs, ha, hlab, ht₁, ht, lt, hpt'⟩ := exists_conj_over hx (σ : D.X.Ω₁ →+* D.X.Ω₁) σ.surjective hφ
  refine ⟨a, ⟨P₀, a₂, t, ε₀, h₂, ht, l₂, lt, fun E => ⟨(hε E).2, ?_⟩, hpt'⟩, hlab, fun hH b κ => ?_⟩
  · have ht₂ := ht.1.w
    refine h₁.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, ht₁, (hε E).1, ← Category.assoc, ht₁]
    · rw [Category.assoc, Category.assoc, ht₂, Over.w (ε₀ E), ← Category.assoc, Over.w (ε₀ E), ht₂]
  · have key := hσU κ _ hφ s hs a ha hlab hH (D.m • b)
    rw [map_nsmul] at key
    exact key

end GlobalTheory.Poinc.GalPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreInvariantVectorFieldsAtGenericPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFields

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  RingHom.ext fun z => by ext <;> simp [dualMap]

theorem dualMapR_eq {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : Chart.dualMapR f = dualMap f :=
  RingHom.ext fun z => by ext <;> simp [dualMap, Chart.dualMapR]

theorem one_left {S : Scheme.{0}} (X G : Over S) [GrpObj G] : (1 : X ⟶ G).left = X.hom ≫ η[G].left := by
  rw [Hom.one_def]; rfl

theorem red_of_isTr {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S]
    {φ : R →+* S} {g : Sp S ⟶ G.left} {v : TanM (𝟙 (Sp R)) G} {w : Sp (DualNumber S) ⟶ G.left}
    (hg : g ≫ G.hom = spMap φ) (h : IsTr G φ g v w) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g := by
  obtain ⟨g', v', h₁, h₂, rfl⟩ := h
  have e0 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    rw [sp_comp]
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; exact Spec.map_id _
  let red : Over.mk (g ≫ G.hom) ⟶ tEpsG (g ≫ G.hom) :=
    Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
      change _ ≫ spMap (algebraMap S (DualNumber S)) ≫ g ≫ G.hom = g ≫ G.hom
      rw [← Category.assoc, e0, Category.id_comp])
  have ef : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (dualMap φ) = φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    exact RingHom.ext fun z => by simp [dualMap]
  have hv : red ≫ v' = 1 := by
    apply Over.OverMorphism.ext
    have hr := congrArg (fun q => q.left) (GlobalTheory.InvFieldBase.redPt_tv G v)
    simp only [Over.comp_left] at hr
    rw [Over.comp_left, one_left, h₂, ← Category.assoc]
    change (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap φ)) ≫ _ = _
    rw [sp_comp, ef, ← sp_comp, Category.assoc]
    change spMap φ ≫ ((GlobalTheory.InvFieldBase.redPt R).left ≫ (tv v).left) = _
    rw [hr, one_left]
    change spMap φ ≫ 𝟙 _ ≫ _ = (g ≫ G.hom) ≫ _
    rw [Category.id_comp, hg]
  have k := congrArg (fun q => q.left) (MonObj.comp_mul red g' v')
  simp only [hv, _root_.mul_one, Over.comp_left] at k
  change red.left ≫ _ = g
  rw [k, h₁, ← Category.assoc]
  change (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S))) ≫ g = g
  rw [e0, Category.id_comp]

theorem isTr_push {R K : Type} [CommRing R] [CommRing K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left)
    (hm : IsGrpPullback A G (spMap x₀) m) (w₀ : TanM (𝟙 (Sp R)) G) (v : TanM (𝟙 (Sp K)) A)
    (hv : (tv v).left ≫ m = spMap (dualMap x₀) ≫ (tv w₀).left) {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (y : Sp (DualNumber B) ⟶ A.left) (hy : IsTr A φ x v y) :
    IsTr G (φ.comp x₀) (x ≫ m) w₀ (y ≫ m) := by
  obtain ⟨g', v', h₁, h₂, rfl⟩ := hy
  obtain ⟨p, q, hp, hq, hpq⟩ := GlobalTheory.CechKS.exists_mul_of_isGrpPullback hm (tEpsG (x ≫ A.hom)) g' v'
    (spMap (algebraMap B (DualNumber B)) ≫ (x ≫ m) ≫ G.hom) (by
      change _ = (spMap (algebraMap B (DualNumber B)) ≫ x ≫ A.hom) ≫ spMap x₀
      rw [Category.assoc x m, hm.1.w]
      simp only [Category.assoc])
  refine ⟨p, q, ?_, ?_, hpq⟩
  · simp only [hp, h₁, Category.assoc]
  · rw [hq, h₂, Category.assoc (spMap (dualMap φ)), hv, ← Category.assoc, sp_comp, dualMap_comp]

def epsOf {L : Type} [CommRing L] (D : L → L) (h1 : D 1 = 0) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = x * D y + y * D x) : L →+* DualNumber L where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (D s)
  map_one' := by ext <;> simp [h1]
  map_zero' := by
    have h0 : D 0 = 0 := by have := ha 0 0; simp at this; exact this
    ext <;> simp [h0]
  map_add' a b := by ext <;> simp [ha]
  map_mul' a b := by ext <;> simp [hm]; ring

theorem eq_of_isTr {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {v : TanM (𝟙 (Sp R)) G} {dd : Fld G.left} (hd : IsInv G v dd) {L : Type} [CommRing L] (φ : R →+* L)
    (y : Sp L ⟶ G.left) (hy : y ≫ G.hom = spMap φ) (D : L → L) (h1 : D 1 = 0) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = x * D y + y * D x) (U : G.left.Opens) (hU : IsAffineOpen U)
    (hyU : ⊤ ≤ y ⁻¹ᵁ U) (hD : ∀ f, valR y U (dd U f) = D (valR y U f)) {w : Sp (DualNumber L) ⟶ G.left}
    (hw : IsTr G φ y v w) : w = spMap (epsOf D h1 ha hm) ≫ y := by
  have r1 := red_of_isTr hy hw
  have e1 : spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ spMap (epsOf D h1 ha hm) = 𝟙 _ := by
    rw [sp_comp]
    have : (TrivSqZeroExt.fstHom L L L).toRingHom.comp (epsOf D h1 ha hm) = RingHom.id L := by
      ext r; simp [epsOf]
    rw [this]; exact Spec.map_id _
  have r2 : spMap (TrivSqZeroExt.fstHom L L L).toRingHom ≫ (spMap (epsOf D h1 ha hm) ≫ y) = y := by
    rw [← Category.assoc, e1, Category.id_comp]
  have hwU := GlobalTheory.CechKS.le_preimage_of_red r1 hyU
  refine GlobalTheory.Points.ext_of_valR hU hwU (GlobalTheory.CechKS.le_preimage_of_red r2 hyU) fun f => ?_
  rw [GlobalTheory.Points.valR_spMap_comp _ _ _ hyU]
  have h0 := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom L L L).toRingHom w U hwU f
  rw [r1] at h0
  ext
  · rw [h0]; simp [epsOf]
  · rw [hd.2 L φ y w U f hy hyU hw, hD]; simp [epsOf]

theorem exists_affine {Ω : Type} [CommRing Ω] [IsLocalRing Ω] {X : Scheme.{0}} (x : Sp Ω ⟶ X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ x ⁻¹ᵁ U := by
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show x.base (IsLocalRing.closedPoint Ω) ∈ (⊤ : X.Opens) from trivial)
  refine ⟨U, hU, fun p _ => ?_⟩
  exact ((IsLocalRing.specializes_closedPoint (R := Ω) p).map x.base.hom.continuous).mem_open U.isOpen hx

theorem exists_basis_bc {R K : Type} [CommRing R] [CommRing K] (x₀ : R →+* K) (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left)
    (hm : IsGrpPullback A G (spMap x₀) m) (hs : Smooth G.hom) {n : ℕ}
    (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) :
    ∃ v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) A),
      ∀ a, (tv (v a)).left ≫ m = spMap (dualMap x₀) ≫ (tv (v' a)).left := by
  obtain ⟨u', hu', hu'l⟩ := GlobalTheory.Heat.CoeffWt.exists_isLieBasis v'
  obtain ⟨u, hu, hul⟩ := GlobalTheory.exists_isLieBasis_baseChange R K x₀ G A m hm hs n u' hu'
  have h := GlobalTheory.Heat.CoeffWt.isGrpPullback_self A
  let b : Fin n → TanM (𝟙 (Sp K)) A := fun j =>
    PullbackSections.mkT (pushHom h (epsR K) (u j)) ((PullbackSections.isTangent_iff h _).1 (hu.1 j))
  have ts : ∀ f : Fin n → TanM (𝟙 (Sp K)) A, tv (∑ i, f i) = ∏ i, tv (f i) := fun f => by
    simp [tv, toMul_sum]
  have hcomb : ∀ (c : Fin n → K) (w : epsR K ⟶ A), IsLieComb c u w ↔
      pushHom h (epsR K) w = tv (∑ i, c i • b i) := fun c w => by
    rw [PullbackSections.isLieComb_iff h, ts]
    rfl
  have hbij : Function.Bijective (Fintype.linearCombination K b) := by
    rw [Function.bijective_iff_existsUnique]
    intro W
    obtain ⟨p, hp⟩ := PullbackSections.push_surj h (tv W)
    have ht : IsTangent p := (PullbackSections.isTangent_iff h p).2 (by rw [hp]; exact PullbackSections.tv_mem W)
    refine (existsUnique_congr fun c => ?_).1 (hu.2 p ht)
    rw [hcomb, hp, Fintype.linearCombination_apply]
    exact ⟨fun e => (PullbackSections.tanM_ext e).symm, fun e => by rw [e]⟩
  refine ⟨(Pi.basisFun K (Fin n)).map (LinearEquiv.ofBijective _ hbij), fun a => ?_⟩
  have e : (Pi.basisFun K (Fin n)).map (LinearEquiv.ofBijective _ hbij) a = b a := by
    simp [Module.Basis.map_apply, Fintype.linearCombination_apply_single]
  rw [e]
  change ((u a).left ≫ 𝟙 _) ≫ m = _
  rw [Category.comp_id, hul a, hu'l a, dualMapR_eq]

theorem der_frac {R : Type} [CommRing R] [IsDomain R] {L : Type} [Field L] (ψ : FractionRing R →+* L)
    (D : L → L) (hl : ∀ x y, D (x * y) = x * D y + y * D x) (h : ∀ r, D (ψ (algebraMap R (FractionRing R) r)) = 0)
    (k : FractionRing R) :
    D (ψ k) = 0 := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) k
  have hy0 : algebraMap R (FractionRing R) y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hψ0 : ψ (algebraMap R (FractionRing R) y) ≠ 0 := (map_ne_zero ψ).2 hy0
  have e : ψ (algebraMap R (FractionRing R) x / algebraMap R (FractionRing R) y) * ψ (algebraMap R (FractionRing R) y) =
      ψ (algebraMap R (FractionRing R) x) := by rw [← map_mul, div_mul_cancel₀ _ hy0]
  have k2 := congrArg D e
  rw [hl, h, h, mul_zero, zero_add] at k2
  exact (mul_eq_zero.1 k2).resolve_left hψ0

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) → ξ ≫ P.A.A.hom = spMap ψ → ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' → (∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∃ (v : Module.Basis (Fin n) (FractionRing R) (TanM (𝟙 (Sp (FractionRing R))) P.A.A)) (dd : Fin n → Fld P.A.A.left), (∀ a, IsInv P.A.A (v a) (dd a)) ∧ ∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δL a (valR ξ O f) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ n v' D Ω _ _ _ φ x' δ dd' _ hx' hinv hδ hval _ g _ δL hδL ψ ξ
    hψ hξA hξ _
  have hm : IsGrpPullback P.A.A t.G (spMap (algebraMap R (FractionRing R)))
      (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) := GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  obtain ⟨v, hv⟩ := exists_basis_bc (algebraMap R (FractionRing R)) t.G P.A.A _ hm t.semi.smooth v'
  choose dd hdd using fun a => GlobalTheory.InvFieldBase.exists_isInv (FractionRing R) P.A.A (v a)
  refine ⟨v, dd, hdd, fun a O f hO => ?_⟩
  obtain ⟨U, hU, hxU⟩ := exists_affine x'
  have hyU : ⊤ ≤ (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) ⁻¹ᵁ U := by
    rw [hξ]
    exact fun p _ => hxU (Set.mem_univ ((spMap (algebraMap Ω (FractionRing Ω))).base p))
  have hyG : (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) ≫ t.G.hom =
      spMap (ψ.comp (algebraMap R (FractionRing R))) := by
    rw [Category.assoc, hm.1.w, ← Category.assoc, hξA, sp_comp]
  have hl : ∀ x y, δL a (x * y) = x * δL a y + y * δL a x := fun x y => by
    rw [(δL a).leibniz, smul_eq_mul, smul_eq_mul]
  have hDy : ∀ f, valR (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) U (dd' a U f) =
      δL a (valR (ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) U f) := by
    intro f
    rw [hξ, GlobalTheory.Points.valR_spMap_comp _ _ _ hxU, GlobalTheory.Points.valR_spMap_comp _ _ _ hxU, hval a U _ hxU, hδL]
  have hc : ∀ k, δL a (ψ k) = 0 := der_frac ψ (δL a) hl fun r => by rw [hψ, hδL, hδ, map_zero]
  have hdual : (dualMap ψ).comp (algebraMap (FractionRing R) (DualNumber (FractionRing R))) =
      (algebraMap (FractionRing Ω) (DualNumber (FractionRing Ω))).comp ψ := by
    ext k <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let g' : tEpsG (ξ ≫ P.A.A.hom) ⟶ P.A.A :=
    Over.homMk (spMap (algebraMap (FractionRing Ω) (DualNumber (FractionRing Ω))) ≫ ξ) (Category.assoc _ _ _)
  let w' : tEpsG (ξ ≫ P.A.A.hom) ⟶ P.A.A :=
    Over.homMk (spMap (dualMap ψ) ≫ (tv (v a)).left) (by
      rw [Category.assoc, Over.w (tv (v a)), hξA]
      change spMap (dualMap ψ) ≫ spMap (algebraMap _ _) ≫ 𝟙 _ = spMap _ ≫ spMap ψ
      rw [Category.comp_id, sp_comp, sp_comp, hdual])
  have htr : IsTr P.A.A ψ ξ (v a) (g' * w').left := ⟨g', w', rfl, rfl, rfl⟩
  have key : (g' * w').left = spMap (epsOf (δL a) (δL a).map_one_eq_zero (map_add _) hl) ≫ ξ := by
    refine hm.1.hom_ext ?_ ?_
    · rw [eq_of_isTr (hinv a) _ _ hyG (δL a) (δL a).map_one_eq_zero (map_add _) hl U hU hyU hDy
        (isTr_push _ _ hm (v' a) (v a) (hv a) ψ ξ _ htr), Category.assoc]
    · rw [Over.w (g' * w')]
      change spMap (algebraMap (FractionRing Ω) (DualNumber (FractionRing Ω))) ≫ ξ ≫ P.A.A.hom =
        (spMap _ ≫ ξ) ≫ P.A.A.hom
      rw [Category.assoc, hξA, sp_comp, sp_comp]
      congr 1
      ext k
      · simp [epsOf, TrivSqZeroExt.algebraMap_eq_inl]
      · simp [epsOf, TrivSqZeroExt.algebraMap_eq_inl, hc]
  rw [← (hdd a).2 (FractionRing Ω) ψ ξ _ O f hξA hO htr, key, GlobalTheory.Points.valR_spMap_comp _ _ _ hO]
  simp [epsOf]

end GlobalTheory.GenFields
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLevelOfFixed
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isCompU_of_equiv {π : Submodule ℂ (UA E n → ℂ)} {w : Pl E} {σ σ' : SmIrr (UL n w)}
    (h : IsCompU π w σ) (e : σ.ρ.Equiv σ'.ρ) : IsCompU π w σ' := by
  obtain ⟨p, hp, -, f, hf0, hfπ, hfe⟩ := h
  let g : σ'.V →ₗ[ℂ] σ.V := e.symm.toLinearEquiv.toLinearMap
  have hg : ∀ x v, g (σ'.ρ x v) = σ.ρ x (g v) := fun x v =>
    LinearMap.congr_fun (e.symm.isIntertwining' x) v
  refine ⟨p, hp, σ'.irred, f ∘ₗ g, ?_, fun v => hfπ _, fun x v => ?_⟩
  · intro h0
    apply hf0
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h0 (e.toLinearEquiv v)
    simpa [g] using this
  · simp only [LinearMap.comp_apply, hg, hfe]

theorem hasLevel_of_fixed {S : Set (Pl E)} (hS : IsSection S) {π : Submodule ℂ (UA E n → ℂ)}
    {K' : ∀ w : Pl E, Subgroup (UL n w)} (h : π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥) : HasLevel S π K' := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine ⟨φ, (Submodule.mem_inf.1 hφ).1, hφ0, fun w hw x hx hk => ?_⟩
  obtain ⟨k, hk, hkx⟩ := hk
  have hxf : x ∈ finU (E := E) (n := n) := hx.1
  have hmem : (⟨x, hxf⟩ : finU (E := E) (n := n)) ∈ globLev S K' := by
    simp only [globLev, Subgroup.mem_iInf, Subgroup.mem_comap, Subgroup.mem_map]
    intro w' hw'
    by_cases hww : w' = w
    · subst hww
      exact ⟨k, hk, hkx⟩
    · have hu : w'.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) := by
        intro he
        exact hww ((hS w).unique ⟨hw', he⟩ ⟨hw, rfl⟩)
      have hker : x ∈ (cLoc w').ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 w') hu
      refine ⟨1, one_mem _, ?_⟩
      simpa using (MonoidHom.mem_ker.1 hker).symm
  have := (Submodule.mem_inf.1 hφ).2 ⟨_, hmem⟩
  simpa [fixed, eig, RF] using this

theorem dimW_ne_zero (lam : InfinitePlace E → DomWeight n) : dimW lam ≠ 0 := by
  unfold dimW
  rw [Finset.prod_ne_zero_iff]
  intro v _
  rw [map_one, LinearMap.trace_one]
  exact_mod_cast Module.finrank_pos.ne'

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSupportedUnitaryPointIntegralCofiniteStatement
section
open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertSupportedUnitaryPoint_integral_cofinite : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ Formalism.MainNotions.StandardLatticesGL3.InertQ D p) ∧ Formalism.MainNotions.StandardLatticesGL3.IntG D (GlobalTheory.NormSum.VacInt.part D (fun p => p ∉ s) y : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  first | exact @GlobalTheory.InertCofinite.intG_part_cofinite | exact GlobalTheory.InertCofinite.intG_part_cofinite | (intros; apply GlobalTheory.InertCofinite.intG_part_cofinite <;> assumption)
end

