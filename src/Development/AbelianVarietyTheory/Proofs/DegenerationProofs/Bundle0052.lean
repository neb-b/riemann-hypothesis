module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightZeroSumOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.LocalWeightUnits

theorem exists_weight_zero_sum_one {A X J : Type} [CommRing A] [AddCommGroup X] [Fintype J] (P : X → AddSubgroup A)
    (one : 1 ∈ P 0) (mul : ∀ u v χ χ', u ∈ P χ → v ∈ P χ' → u * v ∈ P (χ + χ'))
    (ex : ∀ u : A, ∃ a : X →₀ A, (∀ χ, a χ ∈ P χ) ∧ u = a.sum fun _ x => x)
    (un : ∀ a : X →₀ A, (∀ χ, a χ ∈ P χ) → (a.sum fun _ x => x) = 0 → a = 0)
    (g : J → A) (δ : X) (hg : ∀ f, g f ∈ P δ) (hs : Ideal.span (Set.range g) = ⊤) :
    ∃ b : J → A, (∀ f, b f ∈ P 0) ∧ (∀ f, g f ∣ b f) ∧ ∑ f, b f = 1 := by
  classical
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hs.ge (Submodule.mem_top (x := (1 : A))))
  choose a ha hsum using fun f => ex (c f)
  let T : (X →₀ A) →ₗ[A] A := Finsupp.lsum A fun _ => LinearMap.id
  have hT : ∀ a : X →₀ A, T a = a.sum fun _ x => x := fun a => rfl
  let B : X →₀ A := ∑ f, g f • Finsupp.equivMapDomain (Equiv.addLeft δ) (a f) - Finsupp.single 0 1
  have hB : ∀ χ, B χ = ∑ f, g f * a f (-δ + χ) - Finsupp.single (0 : X) (1 : A) χ := fun χ => by
    simp [B]
  have hm : ∀ f χ, g f * a f (-δ + χ) ∈ P χ := fun f χ => by
    simpa using mul _ _ _ _ (hg f) (ha f (-δ + χ))
  have h0 : B = 0 := by
    refine un B (fun χ => ?_) ?_
    · rw [hB]
      refine sub_mem (sum_mem fun f _ => hm f χ) ?_
      rw [Finsupp.single_apply]
      split_ifs with h
      · exact h ▸ one
      · exact zero_mem _
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [← hT, map_sub, map_sum]
        simp only [map_smul]
        simp only [hT, Finsupp.sum_equivMapDomain, ← hsum, smul_eq_mul]
        rw [Finsupp.sum_single_index rfl, sub_eq_zero, ← hc]
        exact Finset.sum_congr rfl fun f _ => mul_comm _ _
  refine ⟨fun f => g f * a f (-δ + 0), fun f => hm f 0, fun f => Dvd.intro _ rfl, ?_⟩
  have := hB 0
  rw [h0, Finsupp.single_eq_same] at this
  exact (sub_eq_zero.1 this.symm)

variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ H}

theorem hasWt_iff {V : H.left.Opens} {u : Γ(H.left, V)} {χ : X} : HasWt i V u χ ↔ GlobalTheory.UU.IsWt i V u χ :=
  ⟨fun h Z t g h₁ h₂ => h Z t g h₂ h₁, fun h Z t g h₁ h₂ => h Z t g h₂ h₁⟩

def wtSpace (i : splitTorus S X ⟶ H) (V : H.left.Opens) (χ : X) : AddSubgroup Γ(H.left, V) where
  carrier := {u | GlobalTheory.UU.IsWt i V u χ}
  zero_mem' := GlobalTheory.UU.isWt_zero χ
  add_mem' := GlobalTheory.UU.IsWt.add
  neg_mem' := fun {u} hu Z t g h₁ h₂ => by rw [map_neg, map_neg, hu Z t g h₁ h₂, mul_neg]

theorem stable_basicOpen {V : H.left.Opens} (hV : Stable i V) {b : Γ(H.left, V)} (hb : HasWt i V b 0) :
    Stable i (H.left.basicOpen b) := by
  intro Y t g h
  have h₁ : ⊤ ≤ g.left ⁻¹ᵁ V := h.trans (g.left.preimage_mono (H.left.basicOpen_le b))
  have e := congrArg Y.left.basicOpen (hb Y t g h₁ (hV Y t g h₁))
  rw [charUnit_zero_val, map_one, _root_.one_mul, Scheme.basicOpen_appLE, Scheme.basicOpen_appLE] at e
  exact ((le_inf le_rfl h).trans e.ge).trans inf_le_right

theorem preimage_le_of_stable {V : H.left.Opens} (hV : Stable i V) :
    (snd (splitTorus S X) H).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) H ≫ i) * snd (splitTorus S X) H).left ⁻¹ᵁ V := by
  let U := (snd (splitTorus S X) H).left ⁻¹ᵁ V
  let Y : Over S := Over.mk (U.ι ≫ (splitTorus S X ⊗ H).hom)
  let j : Y ⟶ splitTorus S X ⊗ H := Over.homMk U.ι rfl
  have h := hV Y (j ≫ fst _ _) (j ≫ snd _ _) (fun y _ => y.2)
  rw [Category.assoc, ← MonObj.comp_mul] at h
  exact fun y hy => h (x := ⟨y, hy⟩) trivial

theorem exists_units {d : ℕ} {i : splitTorus S (Fin d → ℤ) ⟶ H} {V : H.left.Opens} (w : Fin d → Γ(H.left, V)ˣ)
    (hw : ∀ k, GlobalTheory.UU.IsWt i V (w k).val (Pi.single k 1)) :
    ∃ u : Multiplicative (Fin d → ℤ) →* Γ(H.left, V)ˣ, ∀ χ, HasWt i _ (u (Multiplicative.ofAdd χ)).val χ := by
  let e := Pi.basisFun ℤ (Fin d)
  let l : (Fin d → ℤ) →ₗ[ℤ] Additive Γ(H.left, V)ˣ := e.constr ℤ fun k => Additive.ofMul (w k)
  let M : AddSubgroup (Fin d → ℤ) :=
    { carrier := {χ | GlobalTheory.UU.IsWt i _ (Additive.toMul (l χ)).val χ}
      zero_mem' := by
        show GlobalTheory.UU.IsWt i _ (Additive.toMul (l 0)).val 0
        rw [map_zero]; exact GlobalTheory.UU.isWt_one
      add_mem' := fun {a c} ha hc => by
        show GlobalTheory.UU.IsWt i _ (Additive.toMul (l (a + c))).val (a + c)
        rw [map_add (f := _)]; exact GlobalTheory.UU.IsWt.mul ha hc
      neg_mem' := fun {a} ha => by
        show GlobalTheory.UU.IsWt i _ (Additive.toMul (l (-a))).val (-a)
        rw [map_neg]; exact GlobalTheory.UU.IsWt.inv ha }
  have hM : Submodule.span ℤ (Set.range e) ≤ M.toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show GlobalTheory.UU.IsWt i _ (Additive.toMul (l (e k))).val (e k)
    rw [Module.Basis.constr_basis, Pi.basisFun_apply]
    exact hw k
  exact ⟨AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom, fun χ => hasWt_iff.2 (hM (e.mem_span χ))⟩

theorem mem_basicOpen_of_mem {Z : Scheme.{0}} (C : Charts Z) {a a'} {j : C.I} {y : Z} (hy : y ∈ C.W a)
    (h : y ∈ Z.basicOpen (C.r a' j)) : y ∈ Z.basicOpen (C.r a j) := by
  have e := congrArg Z.basicOpen (C.trans a' a j)
  rw [Scheme.basicOpen_mul] at e
  erw [Z.basicOpen_res (C.r a' j) (homOfLE _).op, Z.basicOpen_res (C.r a j) (homOfLE _).op] at e
  exact (e.le ⟨⟨Z.basicOpen_le _ h, hy⟩, h⟩).2.2

theorem main : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), C.Torus c i → ∀ (a) (x : H.left), x ∈ C.W a → ∃ b : Γ(H.left, C.W a), HasWt i (C.W a) b 0 ∧ x ∈ H.left.basicOpen b ∧ Stable i (H.left.basicOpen b) ∧ ∃ u : Multiplicative (Fin d → ℤ) →* Γ(H.left, H.left.basicOpen b)ˣ, ∀ χ, HasWt i _ (u (Multiplicative.ofAdd χ)).val χ := by
  intro K _ H _ _ _ _ _ C d c i hT a x hx
  classical
  obtain ⟨ex, un⟩ := GlobalTheory.functions_graded_by_weights _ H _ i hT.hom (C.W a) (C.aff a) (preimage_le_of_stable (hT.stable a))
  let J := ∀ k : Fin d, {j : C.I // C.wt j = c k}
  let _ : Fintype J := Fintype.ofFinite J
  let g : J → Γ(H.left, C.W a) := fun f => ∏ k, C.r a (f k).1
  have hg : ∀ f, g f ∈ wtSpace i (C.W a) (∑ k : Fin d, Pi.single k 1) := fun f => by
    change GlobalTheory.UU.IsWt i _ (∏ k ∈ Finset.univ, C.r a (f k).1) (∑ k ∈ Finset.univ, Pi.single k 1)
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty => exact GlobalTheory.UU.isWt_one
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact (hasWt_iff.1 (hT.wt a _ k (f k).2)).mul ih
  have hs : Ideal.span (Set.range g) = ⊤ := by
    rw [← (C.aff a).self_le_iSup_basicOpen_iff]
    intro y hy
    choose a' j hj hyj using fun k => hT.bpf k y
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g fun k => ⟨j k, hj k⟩, _, rfl⟩, ?_⟩
    rw [H.left.mem_basicOpen _ y hy, map_prod]
    exact IsUnit.prod_univ_iff.2 fun k => (H.left.mem_basicOpen _ y hy).1 (mem_basicOpen_of_mem C hy (hyj k))
  obtain ⟨b, hb, hd, h1⟩ := exists_weight_zero_sum_one (wtSpace i (C.W a)) GlobalTheory.UU.isWt_one
    (fun _ _ _ _ => GlobalTheory.UU.IsWt.mul) ex un g _ hg hs
  have hu : IsUnit (∑ f, (H.left.presheaf.germ (C.W a) x hx).hom (b f)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, h1, map_one]; exact isUnit_one
  obtain ⟨f, -, hf⟩ := IsLocalRing.exists_of_isUnit_sum hu
  refine ⟨b f, hasWt_iff.2 (hb f), (H.left.mem_basicOpen _ x hx).2 hf,
    stable_basicOpen (hT.stable a) (hasWt_iff.2 (hb f)), ?_⟩
  have hw : ∀ k, IsUnit (resG H.left (H.left.basicOpen_le (b f)) (C.r a (f k).1)) := fun k =>
    isUnit_of_dvd_unit (map_dvd _ ((Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans (hd f)))
      (H.left.toRingedSpace.isUnit_res_basicOpen (b f))
  exact exists_units (fun k => (hw k).unit) fun k => (hasWt_iff.1 (hT.wt a _ k (f k).2)).res _

end GlobalTheory.LocalWeightUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FFTTNeZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem ThetaSys.Test.FF_ne_zero {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)
    (hs : ∀ c : S.perp τ.yy.ker →+ ZMod S.N,
      ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c)
    (T : AddSubgroup S.Gam) (hT : T = S.perp τ.yy.ker) (c : T →+ ZMod S.N) : S.FF T c ≠ 0 := by
  subst hT
  obtain ⟨α, hα, rfl⟩ := hs c
  obtain ⟨k, hk, h⟩ := τ.eq α hα
  intro h0
  have h1 : (⟨S.FF _ (τ.wt α) k, hk⟩ : S.R) = 0 := Subtype.ext (congrFun h0 k)
  rw [h1, map_zero, norm_zero] at h
  exact (mul_pos τ.δ_pos (Real.exp_pos _)).ne h

theorem FF_TT_ne_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) := by
  intro o Ω _ _ _ _ S M U₀ hO hL hT hI hZ hW ξ c
  obtain ⟨x, -, hx, -, hxI⟩ := hZ.2.2.2 ξ ⊤ trivial
  obtain ⟨p, hp, y, hy⟩ := (hL.1 U₀ le_rfl hO.ne x hx).1
  obtain ⟨y₀, hA, -, ⟨τ⟩⟩ := hT x p y hy
  refine τ.FF_ne_zero (hW p y₀ τ).1 _ ?_ c
  rw [← (hI x p y y₀ τ hy hA).2]
  unfold ThetaSys.TT ThetaSys.HH
  rw [hxI]

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FfDivFfMemOfSpecializes
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.FirstIneq

theorem perp_anti_of_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {A B : AddSubgroup S.Gam} (h : A ≤ B) : S.perp B ≤ S.perp A :=
  fun _ ha x hx => ha x (h hx)

theorem ff_mem_ring {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) : S.FF T c k ∈ S.R := by
  unfold ThetaSys.FF
  refine finsum_induction (· ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_
  exact mul_mem (S.R.algebraMap_mem _)
    (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

theorem ff_div_ff_mem_of_specializes : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → S.FF _ c k / S.FF _ c' k' ∈ M.O ξ) := by
  intro o Ω _ _ _ _ S M U₀ hO hLL hT hS hG hW hB hE z ξ c c' k k' _ hs hc _ hd'
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  obtain ⟨x, hxW, hxc, hξx, hI⟩ :=
    hG.2.2.2 ξ ⟨_, M.isOpen_setOf_div (S.FF (S.TT M ξ) c') k'⟩ hd'
  have hH : S.HH M x = S.HH M ξ := by unfold ThetaSys.HH; rw [hI]
  have hTT : S.TT M ξ = S.TT M x := by unfold ThetaSys.TT; rw [hH]
  have hHz : S.HH M z ≤ S.HH M ξ := AddSubgroup.closure_mono (hG.2.1 ξ z hs)
  have hf : S.FF _ c k ∈ M.ringOn U₀ := hO.le (ff_mem_ring S _ c k)
  have hf' : S.FF _ c' k' ∈ M.ringOn U₀ := hO.le (ff_mem_ring S _ c' k')
  have hi : (S.FF _ c' k')⁻¹ ∈ M.ringOn U₀ := hO.FF_unit _ c' k' (hG.1 ξ).1 hd'.1
  refine RatModel.O_le_of_specializes hξx ((hLL.1 U₀ le_rfl hO.ne x hxc).2 _ ?_ ?_)
  · rw [div_eq_mul_inv]
    exact mul_mem hf hi
  intro p _ y hy
  obtain ⟨y₀, hAt, hint, ⟨τ⟩⟩ := hT x p y hy
  have hker : S.HH M ξ = τ.yy.ker := hH ▸ (hS x p y y₀ τ hy hAt).2
  have hperp : S.perp τ.yy.ker = S.TT M ξ := by rw [← hker]; rfl
  obtain ⟨α, hα, hwt⟩ := (hW p y₀ τ).1 (c'.comp (AddSubgroup.inclusion hperp.le))
  have h1 := (hB p y₀ τ hint (S.TT M z) c k (ff_mem_ring S _ c k) (hG.1 z).1).1
    (hperp.le.trans (perp_anti_of_le S hHz))
    (((hG.1 z).1.1.trans (hG.1 z).2.le).trans (hHz.trans hker.le)) α hα
    (fun t h₁ h₂ => by rw [hwt]; exact hc t h₁ (hperp.le h₂))
  have hE' : ∀ (T : AddSubgroup S.Gam), T = S.TT M x → ∀ (c : T →+ ZMod S.N) (k : _),
      M.Div (S.FF T c) k x →
      (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) →
      ‖M.val (gPt p ≫ y) (S.FF T c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N)) := by
    rintro T rfl c k h h'
    exact hE x p y y₀ τ hy hAt c k α h hα h'
  have h2 := hE' _ hTT c' k' hxW (fun t h₁ h₂ => by rw [hwt]; rfl)
  rw [hAt, ← h2] at h1
  set yg := gPt p ≫ y with hyg
  have w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : yg w ∈ (U₀ : Set M.Z) := hy.2 ⟨w, rfl⟩
  have hsp := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton yg w)
  have e1 : M.val yg (S.FF _ c' k') * M.val yg (S.FF _ c' k')⁻¹ = 1 := by
    rw [← RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf') (RatModel.ringOn_le_O hw hi),
      mul_inv_cancel₀ hd'.1, RatModel.val_one]
  rw [div_eq_mul_inv, RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf) (RatModel.ringOn_le_O hw hi),
    norm_mul, ← norm_one (α := PadicAlgCl p), ← e1, norm_mul]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

end GlobalTheory.ZH.FirstIneq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsEEOfSpanWeightSpaces
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem ThetaSys.FF_mem_ring (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) : S.FF T c k ∈ S.R := by
  unfold ThetaSys.FF
  refine finsum_induction (· ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_
  exact mul_mem (S.R.algebraMap_mem _)
    (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

theorem RatModel.span_val_span {M : RatModel o Ω} {J : Type} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z}
    {z : M.Z} (h : y (cPt p) = z) (w : Sp (PadicAlgCl p)) (G : Set (J → Ω))
    (hG : ∀ v ∈ G, ∀ j, v j ∈ M.O ((gPt p ≫ y) w)) :
    Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) '' (Submodule.span (M.O z) G)) =
      Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) '' G) := by
  have hs : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨v, hv, rfl⟩
  suffices H : (∀ j, v j ∈ M.O ((gPt p ≫ y) w)) ∧ (fun j => M.val (gPt p ≫ y) (v j)) ∈
      Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) '' G) from H.2
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨hG v hv, Submodule.subset_span ⟨v, hv, rfl⟩⟩
  | zero =>
    refine ⟨fun j => zero_mem _, ?_⟩
    have : (fun j => M.val (gPt p ≫ y) ((0 : J → Ω) j)) = 0 := funext fun j => RatModel.val_zero _
    rw [this]
    exact zero_mem _
  | add u v _ _ hu hv =>
    refine ⟨fun j => add_mem (hu.1 j) (hv.1 j), ?_⟩
    have : (fun j => M.val (gPt p ≫ y) ((u + v) j)) =
        (fun j => M.val (gPt p ≫ y) (u j)) + fun j => M.val (gPt p ≫ y) (v j) :=
      funext fun j => RatModel.val_add hs (hu.1 j) (hv.1 j)
    rw [this]
    exact add_mem hu.2 hv.2
  | smul a v _ hv =>
    have ha : (a : Ω) ∈ M.O ((gPt p ≫ y) w) := RatModel.O_le_of_specializes (RatModel.gPt_specializes h w) a.2
    refine ⟨fun j => mul_mem ha (hv.1 j), ?_⟩
    have : (fun j => M.val (gPt p ≫ y) ((a • v) j)) =
        (⟨M.val (gPt p ≫ y) a, (mem_OO_iff _).2 (RatModel.norm_val_le_one h a.2)⟩ : OO p) •
          fun j => M.val (gPt p ≫ y) (v j) :=
      funext fun j => RatModel.val_mul hs ha (hv.1 j)
    rw [this]
    exact Submodule.smul_mem _ _ hv.2

theorem RatModel.val_div_mul {M : RatModel o Ω} {K : Type} [Field K] {y : Sp K ⟶ M.Z} {z : M.Z}
    (h : ∀ w, y w ⤳ z) {a b c : Ω} (ha : a ∈ M.O z) (hb : b ∈ M.O z) (hb0 : b ≠ 0) (hb' : b⁻¹ ∈ M.O z)
    (hc : c ∈ M.O z) : M.val y (a / b * c) = M.val y a / M.val y b * M.val y c := by
  have h1 : M.val y b⁻¹ = (M.val y b)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← RatModel.val_mul h hb hb', mul_inv_cancel₀ hb0, RatModel.val_one]
  rw [div_eq_mul_inv, RatModel.val_mul h (mul_mem ha hb') hc, RatModel.val_mul h ha hb', h1, div_eq_mul_inv]

theorem ThetaSys.span_val_eq_testLattice (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens)
    (hA : S.admitted M U₀) {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}
    (τ : S.Test p y₀) (hC : M.Cen U₀ z y) (hAt : S.At M y y₀)
    (hI : ∀ x ∈ S.supI M z, ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ)
    (T : AddSubgroup S.Gam) (hT : T = S.perp τ.yy.ker) (hF : ∀ c : T →+ ZMod S.N, S.FF T c ≠ 0)
    (hα : ∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c)
    (hv : ∀ (c : T →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF T c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) →
      (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) →
      ‖M.val (gPt p ≫ y) (S.FF T c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) :
    Submodule.span (OO p) ((fun (v : S.J → Ω) j => M.val (gPt p ≫ y) (v j)) '' (Submodule.span (M.O z)
      {v | ∃ (c : T →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF T c) k z ∧ x₀ ∈ S.supI M z ∧
        v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)})) = τ.E := by
  subst hT
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hC.2 ⟨w, rfl⟩
  have hs : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  have hR : S.R ≤ M.O ((gPt p ≫ y) w) := hA.1.le.trans (RatModel.ringOn_le_O hw)
  have hinv : ∀ c k, M.Div (S.FF (S.perp τ.yy.ker) c) k z → (S.FF _ c k)⁻¹ ∈ M.O ((gPt p ≫ y) w) :=
    fun c k hk => RatModel.ringOn_le_O hw (hA.1.FF_unit _ c k τ.isoFree hk.1)
  have hval : ∀ c k x₀ i, M.Div (S.FF (S.perp τ.yy.ker) c) k z →
      (fun j => M.val (gPt p ≫ y) (S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i))) =
      fun j => M.val (gPt p ≫ y) (S.th x₀) / M.val (gPt p ≫ y) (S.FF _ c k) *
        y₀ (algebraMap o S.R (S.proj _ c j i)) := by
    intro c k x₀ i hk
    funext j
    rw [RatModel.val_div_mul hs (hR (S.th_mem _)) (hR (S.FF_mem_ring _ _ _)) hk.1 (hinv c k hk)
      (Subalgebra.algebraMap_mem _ _), hAt]
    rfl
  have hnorm : ∀ α k x₀, M.Div (S.FF (S.perp τ.yy.ker) (τ.wt α)) k z → x₀ ∈ S.supI M z →
      (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) →
      ‖M.val (gPt p ≫ y) (S.th x₀) / M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k)‖ = Real.exp (τ.q α / S.N) := by
    intro α k x₀ hk hx hm
    rw [norm_div, hI x₀ hx, hv _ k α hk hm fun _ _ _ => rfl, Real.exp_neg]
    have := τ.δ_pos.ne'
    have := (Real.exp_pos (τ.q α / S.N)).ne'
    field_simp
  rw [RatModel.span_val_span hC.1 w]
  · refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨_, ⟨c, k, x₀, i, hk, hx, rfl⟩, rfl⟩
      obtain ⟨α, hm, rfl⟩ := hα c
      exact ⟨α, _, i, hm, (hnorm α k x₀ hk hx hm).le, hval _ k x₀ i hk⟩
    · rintro _ ⟨α, l, i, hm, hl, rfl⟩
      obtain ⟨k, hk⟩ := hA.2 _ (τ.wt α) τ.isoFree (hF _) z
      obtain ⟨x₀, hx⟩ := hA.1.div z
      have hn := hnorm α k x₀ hk hx hm
      have hv' := hval _ k x₀ i hk
      generalize M.val (gPt p ≫ y) (S.th x₀) / M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k) = l₀ at hn hv'
      have hpos : 0 < ‖l₀‖ := hn ▸ Real.exp_pos _
      have h0 : l₀ ≠ 0 := norm_pos_iff.1 hpos
      have hq : l / l₀ ∈ OO p := by
        rw [mem_OO_iff, norm_div, div_le_one hpos, hn]
        exact hl
      have : (fun j => l * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i))) =
          (⟨l / l₀, hq⟩ : OO p) • fun j => l₀ * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i)) := by
        funext j
        show _ = l / l₀ * (l₀ * _)
        rw [← _root_.mul_assoc, div_mul_cancel₀ _ h0]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨_, k, x₀, i, hk, hx, rfl⟩, hv'⟩)
  · rintro _ ⟨c, k, x₀, i, hk, -, rfl⟩ j
    rw [div_eq_mul_inv]
    exact mul_mem (mul_mem (hR (S.th_mem _)) (hinv c k hk)) (Subalgebra.algebraMap_mem _ _)

theorem isEE_of_span_weightSpaces : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.admitted M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) → (∀ z ∈ U₀, EE.E z = Submodule.span (M.O z) (Set.range fun i => Pi.single i (1 : Ω))) → S.IsEE M U₀ EE := by
  intro o Ω _ _ _ hb S M U₀ EE hA h0 _ hF hα hv hE hU
  refine ⟨hU, fun z p _ y y₀ τ hC hAt => ?_⟩
  rw [hE z (hC.1 ▸ isClosed_singleton_cPt y)]
  obtain ⟨hI, hH⟩ := h0 z p y y₀ τ hC hAt
  exact S.span_val_eq_testLattice M U₀ hA τ hC hAt (fun x hx => (hI x).1 hx) _ (congrArg S.perp hH) (hF z)
    (hα p y₀ τ).1 (hv z p y y₀ τ hC hAt)

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSpanRowsOfForallValuationRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem mem_span_rows_iff_vecMul_inv {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω)
    {J : Type} [Fintype J] [DecidableEq J] {c : Matrix J J Ω} (hc : c.det ≠ 0) (v : J → Ω) :
    v ∈ Submodule.span S (Set.range c) ↔ ∀ j, Matrix.vecMul v c⁻¹ j ∈ S := by
  have hu : IsUnit c.det := isUnit_iff_ne_zero.2 hc
  have key : ∀ a : J → S, ∑ i, a i • c i = Matrix.vecMul (fun i => (a i : Ω)) c := fun a => by
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Subalgebra.smul_def]
  refine (Submodule.mem_span_range_iff_exists_fun S (v := fun i => c i)).trans ?_
  constructor
  · rintro ⟨a, rfl⟩ j
    rw [key, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
    exact (a j).2
  · intro h
    refine ⟨fun j => ⟨_, h j⟩, ?_⟩
    rw [key]
    show Matrix.vecMul (Matrix.vecMul v c⁻¹) c = v
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o]
  {J : Type} [Fintype J] [DecidableEq J]

theorem mem_span_rows_of_forall_valuationRing (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {c : Matrix J J Ω} (hc : c.det ≠ 0) (x : M.Z) (v : J → Ω)
    (h : ∀ ξ : M.Z, ξ ⤳ x → ValuationRing (M.O ξ) → v ∈ Submodule.span (M.O ξ) (Set.range c)) :
    v ∈ Submodule.span (M.O x) (Set.range c) :=
  (mem_span_rows_iff_vecMul_inv _ hc v).2 fun j => M.mem_O_of_forall_valuationRing hn x _ fun ξ hξ hv =>
    (mem_span_rows_iff_vecMul_inv _ hc v).1 (h ξ hξ hv) j

theorem span_rows_eq_of_forall_valuationRing (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {b c : Matrix J J Ω} (hb : b.det ≠ 0) (hc : c.det ≠ 0) (x : M.Z)
    (h : ∀ ξ : M.Z, ξ ⤳ x → ValuationRing (M.O ξ) →
      Submodule.span (M.O ξ) (Set.range b) = Submodule.span (M.O ξ) (Set.range c)) :
    Submodule.span (M.O x) (Set.range b) = Submodule.span (M.O x) (Set.range c) :=
  le_antisymm
    (Submodule.span_le.2 fun v hv => M.mem_span_rows_of_forall_valuationRing hn hc x v fun ξ hξ hr =>
      (h ξ hξ hr).le (Submodule.subset_span hv))
    (Submodule.span_le.2 fun v hv => M.mem_span_rows_of_forall_valuationRing hn hb x v fun ξ hξ hr =>
      (h ξ hξ hr).ge (Submodule.subset_span hv))

end RatModel

theorem exists_lat_of_height_le_one :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o]
      [JacobsonSpace M.Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (J : Type) [Fintype J] [DecidableEq J]
      (b : M.Z → Matrix J J Ω) (D : ∀ ξ : M.Z, Submodule (M.O ξ) (J → Ω)), (∀ z, (b z).det ≠ 0) →
      (∀ z, IsClosed ({z} : Set M.Z) → ∃ W : M.Z.Opens, z ∈ W ∧ ∀ ξ ∈ W, ValuationRing (M.O ξ) →
        Submodule.span (M.O ξ) (Set.range (b z)) = D ξ) →
      ∃ EE : M.Lat J, (∀ z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) (Set.range (b z))) ∧
        ∀ (W : M.Z.Opens) (c : Matrix J J Ω), c.det ≠ 0 →
          (∀ ξ ∈ W, ValuationRing (M.O ξ) → D ξ = Submodule.span (M.O ξ) (Set.range c)) →
          ∀ x ∈ W, EE.E x = Submodule.span (M.O x) (Set.range c) := by
  intro o Ω _ _ _ M _ _ hn J _ _ b D hb h
  have hx : ∀ x : M.Z, ∃ (z : M.Z) (W : M.Z.Opens), x ∈ W ∧ ∀ ξ ∈ W, ValuationRing (M.O ξ) →
      Submodule.span (M.O ξ) (Set.range (b z)) = D ξ := fun x => by
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := closure ({x} : Set M.Z))
      ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    obtain ⟨W, hzW, hW⟩ := h z hzc
    exact ⟨z, W, (specializes_iff_mem_closure.2 hz).mem_open W.isOpen hzW, hW⟩
  choose g U hU hg using hx
  have main : ∀ (W : M.Z.Opens) (c : Matrix J J Ω), c.det ≠ 0 →
      (∀ ξ ∈ W, ValuationRing (M.O ξ) → D ξ = Submodule.span (M.O ξ) (Set.range c)) →
      ∀ x ∈ W, Submodule.span (M.O x) (Set.range (b (g x))) = Submodule.span (M.O x) (Set.range c) :=
    fun W c hc hW x hx => M.span_rows_eq_of_forall_valuationRing hn (hb _) hc x fun ξ hξ hr =>
      (hg x ξ (hξ.mem_open (U x).isOpen (hU x)) hr).trans (hW ξ (hξ.mem_open W.isOpen hx) hr)
  refine ⟨⟨fun x => Submodule.span (M.O x) (Set.range (b (g x))), fun x => ⟨U x, b (g x), hU x, hb _,
    main _ _ (hb _) fun ξ hξ hr => (hg x ξ hξ hr).symm⟩⟩, fun z hz => ?_, main⟩
  obtain ⟨W, hzW, hW⟩ := h z hz
  exact main W _ (hb z) (fun ξ hξ hr => (hW ξ hξ hr).symm) z hzW

end GlobalTheory.ZH
end

