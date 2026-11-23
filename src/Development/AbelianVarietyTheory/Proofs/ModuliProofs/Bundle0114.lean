module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelStructureDescendsFieldExtension
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELDesc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

def tateAlong {k : Type} [Field k]
    {Q Q' : Type} [Group Q] [Group Q'] {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop} (Φ : Q ≃* Q')
    (hact : ∀ c x, Φ (act c x) = act' c (Φ x)) (he : ∀ n x y c, e n x y c → e' n (Φ x) (Φ y) c)
    (I : TateIso D k Q act e) : TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by rw [← hact, I.lin]
  ker := fun n hn a => (map_eq_one_iff _ Φ.injective).trans (I.ker n hn a)
  onto := fun n hn x => by
    rw [← map_eq_one_iff Φ.symm Φ.symm.injective, map_pow, I.onto n hn]
    exact exists_congr fun a => Φ.eq_symm_apply
  tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm a]
  isom := fun n hn a b => he _ _ _ _ (I.isom n hn a b)

theorem tate_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (h : IsGrpPullback G' G f φ) (hI : LBIso L' (L.pull φ)) (act : 𝓞 E → (G ⟶ G)) (act' : 𝓞 E → (G' ⟶ G'))
    (hact : ∀ c, (act' c).left ≫ φ = φ ≫ (act c).left) {k : Type} [Field k] (x : Sp k ⟶ S') (y : Sp k ⟶ S)
    (hy : y = x ≫ f) :
    (∀ I' : TateIso D k (Over.mk x ⟶ G') (fun c z => z ≫ act' c) (fun n z z' c => Out.WeilIs G' L' n z z' (unitOn c)),
      ∃ I : TateIso D k (Over.mk y ⟶ G) (fun c z => z ≫ act c) (fun n z z' c => Out.WeilIs G L n z z' (unitOn c)),
        I.ζ = I'.ζ ∧ ∀ n v, (I.ev n v).left = (I'.ev n v).left ≫ φ) ∧
    (∀ I : TateIso D k (Over.mk y ⟶ G) (fun c z => z ≫ act c) (fun n z z' c => Out.WeilIs G L n z z' (unitOn c)),
      ∃ I' : TateIso D k (Over.mk x ⟶ G') (fun c z => z ≫ act' c) (fun n z z' c => Out.WeilIs G' L' n z z' (unitOn c)),
        I'.ζ = I.ζ ∧ ∀ n v, (I.ev n v).left = (I'.ev n v).left ≫ φ) := by
  subst hy
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have hA : ∀ (c : 𝓞 E) (z : Over.mk x ⟶ G'), Φ (z ≫ act' c) = Φ z ≫ act c := by
    intro c z
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hΦ, Category.assoc, hact]
  have hA' : ∀ (c : 𝓞 E) (z : Over.mk (x ≫ f) ⟶ G), Φ.symm (z ≫ act c) = Φ.symm z ≫ act' c := by
    intro c z
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hA, MulEquiv.apply_symm_apply]
  have hW : ∀ (n : ℕ) (z z' : Over.mk x ⟶ G') (c : kˣ),
      (Out.WeilIs G' L' n z z' (unitOn c) ↔ Out.WeilIs G L n (Φ z) (Φ z') (unitOn c)) := fun n z z' c =>
    GlobalTheory.weilIs_grpPullback_of_comm S S' G G' f φ L L' hL hL' h hI (Over.mk x) n z z' (Φ z) (Φ z') (unitOn c)
      (hΦ z) (hΦ z')
  refine ⟨fun I' => ⟨tateAlong Φ hA (fun n z z' c hz => (hW n z z' c).1 hz) I', rfl, fun n v => hΦ _⟩,
    fun I => ⟨tateAlong Φ.symm hA' (fun n z z' c hz => ?_) I, rfl, fun n v => ?_⟩⟩
  · rw [hW, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hz
  · show _ = (Φ.symm (I.ev n v)).left ≫ φ
    rw [← hΦ, MulEquiv.apply_symm_apply]

theorem detCond_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (a : OAct (𝓞 E) G) (a' : OAct (𝓞 E) G')
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {k : Type} [Field k] (x : Sp k ⟶ S') (y : Sp k ⟶ S)
    (hy : y = x ≫ f) (ρ : k) : DetCond D a' x ρ ↔ DetCond D a y ρ := by
  subst hy
  have key : ∀ (σ : 𝓞 E →+* k) (n : ℕ), LieMult a' x σ n ↔ LieMult a (x ≫ f) σ n := fun σ n =>
    GlobalTheory.LiePull.lieMult_pull (𝓞 E) S S' G G' f φ a a' h hact k x σ n
  exact forall_congr' fun σ => and_congr (imp_congr_right fun _ => key σ _) (imp_congr_right fun _ => key σ _)

private theorem spMap_comp_var2 {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

private theorem exists_algClosed_amalgam_of_charZero {K₀ K K' : Type} [Field K₀] [Field K] [Field K'] [CharZero K'] (i : K₀ →+* K)
    (κ : K₀ →+* K') : ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharZero Ω) (iK : K →+* Ω) (iK' : K' →+* Ω),
      iK.comp i = iK'.comp κ := by
  let := i.toAlgebra
  let := κ.toAlgebra
  have : Nontrivial (K ⊗[K₀] K') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K₀ K K' i.injective κ.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
  let : Field (K ⊗[K₀] K' ⧸ m) := Ideal.Quotient.field m
  let q : K ⊗[K₀] K' →+* AlgebraicClosure (K ⊗[K₀] K' ⧸ m) :=
    (algebraMap (K ⊗[K₀] K' ⧸ m) (AlgebraicClosure (K ⊗[K₀] K' ⧸ m))).comp (Ideal.Quotient.mk m)
  let jL : K →+* K ⊗[K₀] K' := (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').toRingHom
  let jR : K' →+* K ⊗[K₀] K' := (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').toRingHom
  refine ⟨AlgebraicClosure (K ⊗[K₀] K' ⧸ m), inferInstance, inferInstance,
    charZero_of_injective_ringHom (q.comp jR).injective, q.comp jL, q.comp jR, ?_⟩
  ext a
  have hL := (Algebra.TensorProduct.includeLeft : K →ₐ[K₀] K ⊗[K₀] K').commutes a
  have hR := (Algebra.TensorProduct.includeRight : K' →ₐ[K₀] K ⊗[K₀] K').commutes a
  exact congrArg q (hL.trans hR.symm)

theorem isPEL_descends : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g k : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (s : Sp K ⟶ Sp o) (t₀ : TObj g k J b (spMap β₀)) (t : TObj g k J b s) (τ : SAB H (Sp K)), Subring.closure (Set.range a) = ⊤ → s = spMap i ≫ spMap β₀ → TMap t t₀ (spMap i) → IsPEL D a bas ρ t τ → ∃ τ₀ : SAB H (Sp K₀), IsPEL D a bas ρ t₀ τ₀ := by
  intro hL E _ _ _ H D g k J a bas o _ b ρ K₀ K _ _ i β₀ s t₀ t τ hcl hs hT hP
  obtain ⟨φ, hφ, hLφ, hactφ, hgeo⟩ := hP
  obtain ⟨ψ, hψ, hLψ, hptψ, hactψ⟩ := hT
  have := t₀.ab.comm
  have := hφ

  have hpb : IsGrpPullback τ.G t₀.A (spMap i) (φ.hom.left ≫ ψ) :=
    IsGrpPullback.congr (IsGrpPullback.comp (isGrpPullback_of_iso φ) hψ) (Category.id_comp _) rfl
  have hLc : LBIso τ.PP.L (t₀.L.pull (φ.hom.left ≫ ψ)) := by
    obtain ⟨w, hw⟩ := hLψ
    have h2 : LBIso (t.L.pull φ.hom.left) (t₀.L.pull (φ.hom.left ≫ ψ)) :=
      iso_linComb ((isGen_iff w).1 hw) (K := PUnit) (fun _ => φ.hom.left) (fun _ => 1)
    exact LBIso.trans τ.PP.isLB (pull_isLB t.isLB _) (pull_isLB t₀.isLB _) hLφ h2
  have hφl : ∀ j, (τ.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (t.act j).left := fun j => by
    rw [← Over.comp_left, hactφ j, Over.comp_left]
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.oAct_descend_of_generators (𝓞 E) J a K₀ K i t₀.A τ.G (φ.hom.left ≫ ψ) τ.act t₀.act
    hcl hpb (fun j => by rw [← Category.assoc, hφl j, Category.assoc, hactψ j, Category.assoc])
  obtain ⟨τ₀, e, he, hLe, hacte⟩ :=
    GlobalTheory.exists_triple_of_fieldExtension hL E H K₀ K i τ t₀.A (φ.hom.left ≫ ψ) t₀.L r t₀.ab hpb t₀.isLB hLc hr2
  have := he
  have hel : ∀ c, (τ₀.act.act c).left ≫ e.hom.left = e.hom.left ≫ (r.act c).left := fun c => by
    rw [← Over.comp_left, hacte c, Over.comp_left]
  have hpe : IsGrpPullback τ₀.G t₀.A (𝟙 _) e.hom.left := isGrpPullback_of_iso e
  refine ⟨τ₀, e, he, hLe, fun j => by rw [hacte, hr1], ?_⟩
  intro K' _ _ _ x' β hx'

  set κ : K₀ →+* K' := (Spec.preimage x').hom with hκ
  have hxκ : x' = spMap κ := by
    show x' = Spec.map (CommRingCat.ofHom (Spec.preimage x').hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hβ : κ.comp β₀ = β := by
    have h1 : spMap (κ.comp β₀) = spMap β := by rw [← spMap_comp_var2, ← hxκ, hx']
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      have hu := b.unit.map β
      rw [h0, Nat.cast_zero, map_zero] at hu
      exact not_isUnit_zero hu
    · exact h0

  obtain ⟨Ω, _, _, _, iK, iK', hΩ⟩ := exists_algClosed_amalgam_of_charZero i κ
  have hsq : spMap iK' ≫ x' = spMap iK ≫ spMap i := by
    rw [hxκ, spMap_comp_var2, spMap_comp_var2, hΩ]
  have hsΩ : spMap iK ≫ s = spMap (iK.comp (i.comp β₀)) := by
    rw [hs, ← Category.assoc, spMap_comp_var2, spMap_comp_var2]
  have hbr : ∀ z : o, iK (i (β₀ z)) = iK' (β z) := fun z => by
    rw [← hβ]
    exact congrArg (fun F : K₀ →+* Ω => F (β₀ z)) hΩ
  obtain ⟨hdet, I₀, hI₀ζ, hI₀ev⟩ := hgeo Ω (spMap iK) (iK.comp (i.comp β₀)) hsΩ
  have := t₀.dim
  have : Smooth t₀.A.hom := SmoothOfRelativeDimension.smooth g t₀.A.hom
  refine ⟨?_, ?_⟩
  ·
    have d1 := (detCond_pull hpb r τ.act hr2 (spMap iK) (spMap iK' ≫ x') hsq
      ((iK.comp (i.comp β₀)) ρ)).1 hdet
    have d2 : DetCond D r (spMap iK' ≫ x') (iK' (β ρ)) := by
      rw [← hbr ρ]
      exact d1
    have d3 := (GlobalTheory.detCond_iff_of_field_extension E H D (Sp K₀) t₀.A K' Ω iK' x' r (β ρ) inferInstance).1 d2
    exact (detCond_pull hpe r τ₀.act hel x' x' (Category.comp_id _).symm (β ρ)).2 d3
  ·
    obtain ⟨I₁, hI₁ζ, hI₁ev⟩ := (tate_pull t₀.isLB τ.PP.isLB hpb hLc r.act τ.act.act hr2 (spMap iK)
      (spMap iK' ≫ x') hsq).1 I₀
    obtain ⟨I, hI⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D (Sp K₀) t₀.pol r.act K' Ω iK' x').2 I₁ r.hom
    obtain ⟨I', hI'ζ, hI'ev⟩ := (tate_pull t₀.isLB τ₀.PP.isLB hpe hLe r.act τ₀.act.act hel x' x'
      (Category.comp_id _).symm).2 I
    refine ⟨I', ?_, fun j => ?_⟩
    · rw [hI'ζ]
      apply iK'.injective
      rw [← (hI k hk).1, hI₁ζ, hI₀ζ]
      simp only [RingHom.comp_apply]
      exact hbr _
    · apply Over.OverMorphism.ext
      rw [Over.comp_left, ← hI'ev]
      show (I.ev k (bas (Pi.single j 1))).left = x' ≫ (t₀.pt j).left
      have ep := ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K' Ω iK').1 (Sp K') (Sp Ω) (𝟙 _) (𝟙 _) (spMap iK')
        IsPullback.of_id_snd).1
      apply ep.left_cancellation
      have e1 : (I₁.ev k (bas (Pi.single j 1))).left = spMap iK' ≫ (I.ev k (bas (Pi.single j 1))).left := by
        rw [(hI k hk).2 (bas (Pi.single j 1)), Over.comp_left]
        rfl
      have e2 : (I₀.ev k (bas (Pi.single j 1))).left ≫ φ.hom.left = spMap iK ≫ (t.pt j).left := by
        rw [← Over.comp_left, hI₀ev j, Over.comp_left]
        rfl
      rw [← e1, hI₁ev, ← Category.assoc, e2, Category.assoc, hptψ j, ← Category.assoc, ← hsq, Category.assoc]
      rfl

end GlobalTheory.PELDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometry
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {g : ℕ}

theorem exists_fibre_unif {t : SAB H S} {y : Sp ℂ ⟶ S} {t₁ : SAB H (Sp ℂ)} (m : SABMap t₁ t y)
    {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    {e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e) (hr : ReadsPeriods t unitOn D ty P e) :
    ∃ e₁ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t₁.G), (∀ z, (e₁ z).left ≫ m.φ = (e z).left) ∧
      (∀ z w, e₁ (z + w) = e₁ z * e₁ w) ∧ Function.Surjective e₁ ∧ ReadsPeriods t₁ unitOn D ty P e₁ ∧
      ∀ (g₀ : ℕ) (u : HolUnif t₁.G t₁.PP.L g₀), ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₁ (h z) = u.ex z := by
  obtain ⟨β, hβ⟩ := exists_pointEquiv m.cart
  have hiso : LBIso t₁.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  refine ⟨fun z => β.symm (e z), ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    have h1 := hβ (β.symm (e z))
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  · intro z w
    simp only [he.1 z w, map_mul]
  · intro x
    obtain ⟨z, hz⟩ := he.2.1 (β x)
    exact ⟨z, by simp [hz]⟩
  · refine ⟨fun z => ?_, fun a z => ?_, fun k a a₂ c hk hc => ?_⟩
    · rw [MulEquiv.map_eq_one_iff]
      exact hr.1 z
    · apply β.injective
      rw [MulEquiv.apply_symm_apply, hr.2.1 a z]
      apply Over.OverMorphism.ext
      rw [hβ, Over.comp_left, Over.comp_left, Category.assoc, m.act a, ← Category.assoc, ← hβ,
        MulEquiv.apply_symm_apply]
    · have H := hr.2.2 k a a₂ c hk hc
      have hL : t.PP.L.IsLB := t.PP.isLB
      have hL₁ : t₁.PP.L.IsLB := t₁.PP.isLB
      let T : Over (Sp ℂ) := 𝟙_ (Over (Sp ℂ))
      have hy : y = T.hom ≫ y := (Category.id_comp y).symm
      let lift : (Over.mk y ⟶ t.G) → (Over.mk (T.hom ≫ y) ⟶ t.G) := fun x =>
        Over.homMk x.left (by simp [T])
      rw [GlobalTheory.weilIs_grpPullback_of_comm S (Sp ℂ) t.G t₁.G y m.cm.F t.PP.L t₁.PP.L hL hL₁ m.cart hiso T (k : ℤ)
        _ _ (lift (e ((k : ℂ)⁻¹ • P a))) (lift (e ((k : ℂ)⁻¹ • P a₂))) (unitOn c)
        (by rw [← hβ, MulEquiv.apply_symm_apply]; rfl) (by rw [← hβ, MulEquiv.apply_symm_apply]; rfl)]
      exact weilIs_congr hy rfl rfl H
  · intro g₀ u
    have hc : {z | β (u.ex z) = 1}.Countable := by
      have := u.discrete
      have : Countable u.Λ := (TopologicalSpace.separableSpace_iff_countable).mp inferInstance
      have h2 : {z | β (u.ex z) = 1} = (u.Λ : Set (Fin g₀ → ℂ)) := by
        ext z
        simp only [Set.mem_ofPred_eq, MulEquiv.map_eq_one_iff, SetLike.mem_coe]
        exact u.ker z
      rw [h2]
      exact Set.countable_coe_iff.mp this
    have hhol : IsHolTo Set.univ (fun z => (β (u.ex z)).left) := by
      unfold IsHolTo
      intro U f
      have h1 := u.hol (m.cm.F ⁻¹ᵁ U) ((m.cm.F.app U).hom f)
      simp only [hβ, Set.mem_univ, true_and]
      exact h1
    obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP he hr.1 (e₀ := fun z => β (u.ex z))
      (fun z w => by simp only [u.ex_add, map_mul]) (β.surjective.comp u.ex_onto) hhol hc
    exact ⟨h, fun z => by rw [MulEquiv.symm_apply_eq]; exact hh z⟩

private theorem eq_of_left_comp_sabMap_phi_eq {S : Scheme.{0}} {t₁ : SAB H (Sp ℂ)} {t : SAB H S} {y : Sp ℂ ⟶ S}
    (m : SABMap t₁ t y) {x x' : 𝟙_ (Over (Sp ℂ)) ⟶ t₁.G} (h : x.left ≫ m.φ = x'.left ≫ m.φ) : x = x' := by
  obtain ⟨β, hβ⟩ := exists_pointEquiv m.cart
  apply β.injective
  apply Over.OverMorphism.ext
  rw [hβ, hβ]
  exact h

private theorem comp_left_eq_toUnit_comp_left {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {G : Over X} (s : 𝟙_ (Over X) ⟶ G) :
    y ≫ s.left = (toUnit (Over.mk y) ≫ s).left := by
  rw [Over.comp_left]
  congr 1

theorem point_eq_iff_isometry : ThetaUnifAV → Out.Laws → (∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u
    : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g →
    ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F
    z) = u.ex z ≫ f) → (∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α
    : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α → p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp
    k)) ⟶ P.A) (c
    : kˣ), 0 < n → n.Coprime p → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn
    c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) → LBIso (abelian₂ P.A (lbPow P.L
    d)) (abelian₂ P.A (P'.L.pull α.left))) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField
    E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b
    : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s'
    : S' ⟶ Sp B') (f
    : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
    o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
    : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b'
    : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s''
    : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o''
    : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f'
    : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫
    f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫
    f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s
    : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
    l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' D'' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (t'
    : D.La →ₗ[𝓞 E] D''.La) (P : D'.La →+ (Fin g → ℂ)) (P' : D''.La →+ (Fin g → ℂ)) (y y'
    : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶
    Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧
    Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e
    0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂
    : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ)
    / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) → (y' ≫ Xo.s = spMap σ ∧ IsPeriod
    D'' ty P' ∧ ((∀ z w, e' (z + w) = e' z * e' w) ∧ Function.Surjective e' ∧ IsHolTo Set.univ
    (fun z => (e' z).left) ∧ (∀ w, ∃! v : epsPt y' ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e'
    z).left) w v.left) ∧ (∀ v : epsPt y' ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ
    ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left)) ∧
    (∀ z, e' z = 1 ↔ z ∈ (P').range) ∧ (∀ (a : 𝓞 E) z, e' (fun k => ty k (a
    : E) * z k) = e' z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D''.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D''.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P'
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e' ((l.M : ℂ)⁻¹ • P' (t' a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e' ((l.A : ℂ)⁻¹ • P' (t' a))) → (y = y' ↔ ∃ (gam : D'.La ≃ₗ[𝓞
    E] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D''.EF (gam a) (gam
    b) = D'.EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), ∃ x, gam (t a) = t' a + l.M • x) ∧ (∀ a, ∃ x, gam (t
    a) = t' a + l.A • x) ∧ ∀ a, P' (gam a) = h (P a)) := by
  intro hT hLaws hA hW hBC hComp hAb hMod E _ _ _ H D l Xo σ g ty hpq hρ hty D' D'' t t' P P' y y' e e' hy hy'
  obtain ⟨hys, hP, hexp, hker, hact, hweil, heta, hetaA⟩ := hy
  obtain ⟨hys', hP', hexp', hker', hact', hweil', heta', hetaA'⟩ := hy'
  have hx : IsExp e := hexp
  have hx' : IsExp e' := hexp'
  have hr : ReadsPeriods Xo.univ.t unitOn D' ty P e := ⟨hker, hact, hweil⟩
  have hr' : ReadsPeriods Xo.univ.t unitOn D'' ty P' e' := ⟨hker', hact', hweil'⟩
  have hM : 0 < l.M := by
    have := l.three_le
    omega
  constructor
  · rintro rfl
    obtain ⟨gam, h, hEF, hPh, heh⟩ := exists_isometry hP hP' hx hx' hr hr'
    refine ⟨gam, h, hEF, fun a ha => ?_, fun a => ?_, hPh⟩
    · rw [← div_eq_iff hP'.2.1 hx'.1 hker' hM, ← heta' a ha, heta a ha, ← heh, map_smul, hPh]
    · rw [← div_eq_iff hP'.2.1 hx'.1 hker' l.A_pos, ← hetaA' a, hetaA a, ← heh, map_smul, hPh]
  · rintro ⟨gam, h, hEF, hMl, hAl, hPh⟩
    let b : Base l ℂ := baseOfEmb σ
    obtain ⟨o₁, ⟨m₁⟩⟩ := hBC E H D l (KA l) ℂ (baseKA l) b σ Xo.X (Sp ℂ) Xo.s (𝟙 _) y rfl rfl
      (by simp [hys]) Xo.univ
    obtain ⟨o₂, ⟨m₂⟩⟩ := hBC E H D l (KA l) ℂ (baseKA l) b σ Xo.X (Sp ℂ) Xo.s (𝟙 _) y' rfl rfl
      (by simp [hys']) Xo.univ
    obtain ⟨e₁, he₁, ha₁, hs₁, hr₁, hu₁⟩ := exists_fibre_unif m₁.toSABMap hP hx hr
    obtain ⟨e₂, he₂, ha₂, hs₂, hr₂, hu₂⟩ := exists_fibre_unif m₂.toSABMap hP' hx' hr'
    have p₁ := hAb E H D l ℂ b (Sp ℂ) (𝟙 _) o₁
    have p₂ := hAb E H D l ℂ b (Sp ℂ) (𝟙 _) o₂
    obtain ⟨m, hm⟩ := exists_sabMap hT hLaws.globalFns hA hW o₁ o₂ p₁ p₂ hP hP' ha₁ hs₁ hs₂ hr₁ hr₂ hu₁ hu₂
      gam h hEF hPh
    have shift : ∀ (n : ℕ), 0 < n → ∀ (a : D.La) (x : D''.La), gam (t a) = t' a + n • x →
        e₂ (h ((n : ℂ)⁻¹ • P (t a))) = e₂ ((n : ℂ)⁻¹ • P' (t' a)) := by
      intro n hn a x hgx
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have h1 : e₂ ((n : ℂ)⁻¹ • P' (n • x)) = 1 := by
        rw [hr₂.1, AddMonoidHom.mem_range]
        refine ⟨x, ?_⟩
        rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn', one_smul]
      rw [map_smul, ← hPh, hgx, map_add (f := _), smul_add, ha₂, h1, _root_.mul_one]
    have eta₁ : ∀ a, o₁.eta a = e₁ ((l.M : ℂ)⁻¹ • P (t a)) ∨
        a ∉ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
      intro a
      by_cases ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)
      · left
        refine eq_of_left_comp_sabMap_phi_eq m₁.toSABMap ?_
        exact ((m₁.eta a).trans ((comp_left_eq_toUnit_comp_left y _).trans
          (congrArg Over.Hom.left (heta a ha)))).trans (he₁ _).symm
      · exact Or.inr ha
    have eta₂ : ∀ a, o₂.eta a = e₂ ((l.M : ℂ)⁻¹ • P' (t' a)) ∨
        a ∉ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
      intro a
      by_cases ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)
      · left
        refine eq_of_left_comp_sabMap_phi_eq m₂.toSABMap ?_
        exact ((m₂.eta a).trans ((comp_left_eq_toUnit_comp_left y' _).trans
          (congrArg Over.Hom.left (heta' a ha)))).trans (he₂ _).symm
      · exact Or.inr ha
    have etaA₁ : ∀ a, o₁.etaA a = e₁ ((l.A : ℂ)⁻¹ • P (t a)) := fun a =>
      eq_of_left_comp_sabMap_phi_eq m₁.toSABMap (((m₁.etaA a).trans ((comp_left_eq_toUnit_comp_left y _).trans
        (congrArg Over.Hom.left (hetaA a)))).trans (he₁ _).symm)
    have etaA₂ : ∀ a, o₂.etaA a = e₂ ((l.A : ℂ)⁻¹ • P' (t' a)) := fun a =>
      eq_of_left_comp_sabMap_phi_eq m₂.toSABMap (((m₂.etaA a).trans ((comp_left_eq_toUnit_comp_left y' _).trans
        (congrArg Over.Hom.left (hetaA' a)))).trans (he₂ _).symm)
    obtain ⟨mo⟩ := exists_objMap o₁ o₂ m
      (fun a ha => by
        obtain ⟨x, hgx⟩ := hMl a ha
        rw [(eta₁ a).resolve_right (not_not_intro ha), (eta₂ a).resolve_right (not_not_intro ha), hm,
          shift l.M hM a x hgx])
      (fun a => by
        obtain ⟨x, hgx⟩ := hAl a
        rw [etaA₁ a, etaA₂ a, hm, shift l.A l.A_pos a x hgx])
    obtain ⟨m₃, -⟩ := ((hComp E H D l (KA l) ℂ ℂ (baseKA l) b b Xo.X (Sp ℂ) (Sp ℂ) Xo.s (𝟙 _) (𝟙 _)
      Xo.univ o₂ o₁).2 y' (𝟙 _) m₂).1 mo
    obtain ⟨f₀, -, huniq⟩ := hMod E H D l Xo ℂ b σ (Sp ℂ) (𝟙 _) o₁ inferInstance rfl rfl
    have k₁ := huniq y ⟨by simp [hys], ⟨m₁⟩⟩
    have k₂ := huniq (𝟙 _ ≫ y') ⟨by simp [hys'], ⟨m₃⟩⟩
    rw [Category.id_comp] at k₂
    exact k₁.trans k₂.symm

end GlobalTheory.UnifPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKernelTrivialOfOpenCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem kTriv_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.KTriv (G i) (M i)) → Out.KTriv A L := by
  intro S I U A _ G _ ψ hU hG L M hL hM hLM hA hGA hK
  rw [GlobalTheory.UU.kTriv_iff_forall]
  intro T x hx
  apply over_ext hU
  intro i T' r
  obtain ⟨y, hy⟩ := exists_lift (hG i).1 (r ≫ x)
  have hpush : pushPt (hG i).1.w y = r ≫ x := by
    ext1
    exact hy.symm
  have hyK : GlobalTheory.UU.InK (G i) (M i) y :=
    GlobalTheory.UU.inK_of_push (hG i) hL (hM i) (hLM i) y (hpush ▸ hx.comp r)
  have hy1 : y = 1 := (GlobalTheory.UU.kTriv_iff_forall.1 (hK i)) T' y hyK
  have hsq : (r ≫ x) * (r ≫ x) = r ≫ x := by
    ext1
    rw [((hG i).2 T' y y (r ≫ x) (r ≫ x) hy hy), hy, hy1, _root_.mul_one]
  have h1 : r ≫ x = 1 := by simpa using hsq
  rw [h1]
  simp

end GlobalTheory.CoverGlue
end

