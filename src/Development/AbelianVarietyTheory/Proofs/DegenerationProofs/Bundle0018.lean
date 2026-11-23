module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinearIndependentOnFibresOfClosedPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FibreLinInd

theorem geometric_of_field (G Z : Scheme.{0}) (f : G ⟶ Z) [Flat f]
    [LocallyOfFinitePresentation f] (L : LB G) (r : ℕ) (s : Fin r → LB.Sec L) (z : Z)
    (K : Type) [Field K] (x : Sp K ⟶ Z) (hx : Set.range x = {z})
    (hz : ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x →
            ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0)
    (K' : Type) [Field K'] [IsAlgClosed K'] (x' : Sp K' ⟶ Z) (hx' : Set.range x' = {z})
    (c : Fin r → K') (hc : ∀ (g : Sp K' ⟶ G) (j : L.ι), g ≫ f = x' →
            ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) : c = 0 := by
  classical
  obtain ⟨P, p, π, h1, h2, h3, h4⟩ := exists_fibrePower f r
  have hxt : ∀ t, x t = z := fun t => by
    rw [← Set.mem_singleton_iff, ← hx]
    exact ⟨t, rfl⟩
  let t₀ : Sp K := IsLocalRing.closedPoint K
  obtain ⟨a, ha⟩ := exists_det_ne_zero
    (fun (a : {g : Sp K ⟶ G // g ≫ f = x} × L.ι) i => valF a.1.1 (L.U a.2) ((s i).f a.2))
    fun c hc => hz c fun g j hg => hc (⟨g, hg⟩, j)
  let j : Fin r → L.ι := fun k => (a k).2
  let U : P.Opens := LB.wchart L π j
  have hU : ∀ k, U ≤ π k ⁻¹ᵁ L.U (j k) := LB.wchart_le L π j
  let M : Matrix (Fin r) (Fin r) Γ(P, U) :=
    Matrix.of fun k i => (π k).appLE (L.U (j k)) U (hU k) ((s i).f (j k))
  have hM : ∀ {K : Type} [Field K] (h : Sp K ⟶ P) (hh : ⊤ ≤ h ⁻¹ᵁ U), evalHom h U hh M.det =
      (Matrix.of fun k i => valF (h ≫ π k) (L.U (j k)) ((s i).f (j k))).det := by
    intro K _ h hh
    rw [RingHom.map_det]
    congr 1
    ext k i
    exact evalHom_appLE h U hh (π k) _ (hU k) _
  let O : P.Opens := P.basicOpen M.det
  have hmem : z ∈ p '' (O : Set P) := by
    obtain ⟨h, hp, hπ⟩ := h4 (Sp K) x (fun k => (a k).1.1) fun k => (a k).1.2
    have hle : ⊤ ≤ h ⁻¹ᵁ U := by
      intro t ht
      refine Set.mem_iInter.2 fun k => ?_
      have hk : ⊤ ≤ (a k).1.1 ⁻¹ᵁ L.U (j k) := by
        by_contra hn
        exact ha (Matrix.det_eq_zero_of_row_eq_zero k fun i => dif_neg hn)
      have := hk ht
      rw [← hπ k] at this
      exact this
    refine ⟨h t₀, (mem_basicOpen_iff h U hle M.det t₀).2 ?_, ?_⟩
    · rw [hM]
      simp only [hπ]
      exact ha
    · rw [← Scheme.Hom.comp_apply, hp, hxt]
  obtain ⟨w, hw, rfl⟩ := hmem
  let t : Sp K' := IsLocalRing.closedPoint K'
  have ht : x' t = p w := by
    rw [← Set.mem_singleton_iff, ← hx']
    exact ⟨t, rfl⟩
  obtain ⟨h, hh⟩ := exists_lift (O.ι ≫ p) x' ⟨w, hw⟩ t ht.symm
  have hO : (h ≫ O.ι) t ∈ O := (h t).2
  have hle : ⊤ ≤ (h ≫ O.ι) ⁻¹ᵁ U := (top_le_iff _ U t).2 (P.basicOpen_le _ hO)
  have hd := (mem_basicOpen_iff _ U hle M.det t).1 hO
  rw [hM] at hd
  refine Matrix.eq_zero_of_mulVec_eq_zero hd (funext fun k => ?_)
  have := hc ((h ≫ O.ι) ≫ π k) (j k) (by rw [Category.assoc, h3, Category.assoc, hh])
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this

theorem linearIndependent_on_fibres_of_closedPoints :
    ∀ (G Z : Scheme.{0}) (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (f : G ⟶ Z) [Flat f] [LocallyOfFinitePresentation f] (L : LB G), L.IsLB → ∀ (r : ℕ) (s : Fin r → LB.Sec L), let P : Z → Prop := fun z => ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Z), Set.range x = {z} → ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x → ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0; (∀ z, IsClosed ({z} : Set Z) → ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Z), Set.range x = {z} ∧ ∀ c : Fin r → K, (∀ (g : Sp K ⟶ G) (j : L.ι), g ≫ f = x → ∑ i, c i * valF g (L.U j) ((s i).f j) = 0) → c = 0) → ∀ z, P z := by
  intro G Z π _ f _ _ L hL r s P h z
  let U : Z.Opens := ⟨{z | P z}, isOpen_setOf_linearIndependent_on_fibres G Z f L hL r s⟩
  have hU : U = ⊤ := (GlobalTheory.jacobson_closedPoints_tools_int Z π).2.2.1 U ⊤ fun y hy => by
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    obtain ⟨K, _, x, hx, hz⟩ := h y hy
    intro K' _ _ x' hx' c hc
    exact geometric_of_field G Z f L r s y K x hx hz K' x' hx' c hc
  have : z ∈ U := by rw [hU]; trivial
  exact this

end GlobalTheory.FibreLinInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace SemiAbTorsion

theorem finite_pow_eq_one_of_extension {T G B : Type*} [Group T] [CommGroup G] [Group B]
    (i : T →* G) (q : G →* B) (hi : Function.Injective i) (hk : ∀ x, q x = 1 → ∃ t, i t = x)
    (n : ℕ) (hT : Finite {t : T // t ^ n = 1}) (hB : Finite {b : B // b ^ n = 1}) :
    Finite {x : G // x ^ n = 1} := by
  let f : {x : G // x ^ n = 1} → {b : B // b ^ n = 1} :=
    fun x => ⟨q x.1, by rw [← map_pow, x.2, map_one]⟩
  refine Set.finite_univ_iff.mp (Set.Finite.of_finite_fibers f (Set.toFinite _) fun b hb => ?_)
  obtain ⟨x₀, -, rfl⟩ := hb
  rw [Set.univ_inter, ← Set.finite_coe_iff]
  have key : ∀ x : f ⁻¹' {f x₀}, ∃ t : {t : T // t ^ n = 1}, i t.1 = x.1.1 / x₀.1 := by
    intro x
    have hx : q x.1.1 = q x₀.1 := congrArg Subtype.val x.2
    obtain ⟨t, ht⟩ := hk (x.1.1 / x₀.1) (by rw [map_div, hx, div_self'])
    refine ⟨⟨t, hi ?_⟩, ht⟩
    rw [map_pow, ht, div_pow, x.1.2, x₀.2, map_one, div_one]
  choose g hg using key
  refine Finite.of_injective g fun x y h => Subtype.ext (Subtype.ext ?_)
  have := hg x
  rw [h, hg y] at this
  exact (div_left_inj.mp this).symm

theorem finite_chars_pow_eq_one (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (R : Type)
    [CommRing R] [IsDomain R] {n : ℕ} (hn : 1 ≤ n) :
    Finite {t : Multiplicative X →* Rˣ // t ^ n = 1} := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : AddGroup.FG X := Module.Finite.iff_addGroup_fg.mp inferInstance
  obtain ⟨S, hS, hfin⟩ := (Group.fg_iff.mp (inferInstance : Group.FG (Multiplicative X)))
  haveI : Finite S := hfin.to_subtype
  let g : {t : Multiplicative X →* Rˣ // t ^ n = 1} → (S → rootsOfUnity n R) := fun t s =>
    ⟨t.1 s.1, (mem_rootsOfUnity _ _).2 (by simpa using DFunLike.congr_fun t.2 s.1)⟩
  refine Finite.of_injective g fun a b h => Subtype.ext ?_
  refine MonoidHom.eq_of_eqOn_dense hS fun s hs => ?_
  exact congrArg Subtype.val (congrFun h ⟨s, hs⟩)

theorem finite_ringHom (A F : Type) [CommRing A] [CommRing F] [Finite F]
    [Algebra.FiniteType ℤ A] : Finite (A →+* F) := by
  obtain ⟨S, hS⟩ := (inferInstance : Algebra.FiniteType ℤ A).out
  refine Finite.of_injective (fun (φ : A →+* F) (s : S) => φ s.1) fun a b h => ?_
  have : a.toIntAlgHom = b.toIntAlgHom :=
    AlgHom.ext_of_adjoin_eq_top hS fun s hs => congrFun h ⟨s, hs⟩
  ext x
  exact DFunLike.congr_fun this x

theorem finite_hom_range_subset {X : Scheme.{0}} (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π]
    (F : CommRingCat.{0}) [Finite F] (V : X.Opens) (hV : IsAffineOpen V) :
    {f : Spec F ⟶ X | Set.range f ⊆ V}.Finite := by
  have h : LocallyOfFiniteType (hV.fromSpec ≫ π) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV.fromSpec ≫ π)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  have e : φ.hom = algebraMap ℤ Γ(X, V) := RingHom.ext_int _ _
  have h' : (algebraMap ℤ Γ(X, V)).FiniteType := e ▸ h
  have : Algebra.FiniteType ℤ Γ(X, V) := RingHom.finiteType_algebraMap.mp h'
  haveI := finite_ringHom Γ(X, V) F
  refine (Set.finite_range fun ψ : Γ(X, V) →+* F =>
    Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec).subset fun f hf => ?_
  have hf' : Set.range f ⊆ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hf
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec f hf')
  refine ⟨ψ.hom, ?_⟩
  change Spec.map ψ ≫ _ = _
  rw [hψ, IsOpenImmersion.lift_fac]

theorem finite_points_over {Z : Scheme.{0}} (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (G : Over Z)
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (F : Type) [Field F] [Finite F]
    (t : Sp F ⟶ Z) : Finite (Over.mk t ⟶ G) := by
  let pt : Sp F := default
  have hpt : ∀ y : Sp F, y = pt := fun y => Subsingleton.elim _ _
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (t pt)) isOpen_univ
  have hc : IsCompact (G.hom ⁻¹ᵁ U : Set G.left) :=
    QuasiCompact.isCompact_preimage (f := G.hom) _ U.isOpen hU.isCompact
  obtain ⟨s, hs, hsU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens).mp hc
  have hfin : (⋃ V ∈ s, {f : Sp F ⟶ G.left | Set.range f ⊆ V.1}).Finite :=
    hs.biUnion fun V _ => finite_hom_range_subset (G.hom ≫ π) (CommRingCat.of F) V.1 V.2
  haveI := hfin.to_subtype
  have hm : ∀ x : Over.mk t ⟶ G,
      x.left ∈ ⋃ V ∈ s, {f : Sp F ⟶ G.left | Set.range f ⊆ V.1} := by
    intro x
    have h1 : x.left pt ∈ G.hom ⁻¹ᵁ U := by
      change (x.left ≫ G.hom) pt ∈ U
      rw [Over.w x]
      exact hxU
    rw [hsU] at h1
    simp only [TopologicalSpace.Opens.mem_iSup] at h1
    obtain ⟨V, hV, hx⟩ := h1
    refine Set.mem_biUnion hV ?_
    rintro _ ⟨y, rfl⟩
    rw [hpt y]
    exact hx
  exact Finite.of_injective (fun x => (⟨x.left, hm x⟩ : (⋃ V ∈ s,
    {f : Sp F ⟶ G.left | Set.range f ⊆ V.1} : Set _)))
    fun a b h => Over.OverMorphism.ext (congrArg Subtype.val h)

theorem comp_pow_points {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) (g : T ⟶ A)
    (n : ℕ) : f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

end SemiAbTorsion

open SemiAbTorsion

theorem semiAbelian_torsion_finite_and_closedPoint_finiteOrder : (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) → (∀ (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], Nonempty (TorusExtension G) → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ G // x ^ n = 1}) ∧ (∀ (Z : Scheme.{0}) (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (G : Over Z) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (w : G.left), IsClosed ({w} : Set G.left) → ∃ n : ℕ, 1 ≤ n ∧ ∀ (K : Type) [Field K] (t : Sp K ⟶ Z) (x : Over.mk t ⟶ G), Set.range x.left = {w} → x ^ n = 1) := by
  intro hB
  refine ⟨?_, ?_⟩
  · rintro K _ _ G _ _ ⟨E⟩ n hn
    letI := E.addCommGroup
    letI := E.finite
    letI := E.grpB
    haveI := E.q_hom
    haveI := E.i_hom
    have hk := E.isKernel
    refine finite_pow_eq_one_of_extension (IsMonHom.monoidHom E.i (𝟙_ (Over (Sp K))))
      (IsMonHom.monoidHom E.q (𝟙_ (Over (Sp K)))) ?_ ?_ n ?_ (hB K E.B E.isAbelian n hn)
    · intro a b h
      exact hk.hom_ext h (toUnit_unique _ _)
    · intro x hx
      have hx' : x ≫ E.q = 1 := hx
      exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
    · haveI : IsDomain Γ((𝟙_ (Over (Sp K))).left, ⊤) :=
        inferInstanceAs (IsDomain Γ(Sp K, ⊤))
      haveI := finite_chars_pow_eq_one E.X Γ((𝟙_ (Over (Sp K))).left, ⊤) hn
      let e := splitTorusPointsEquiv (Sp K) E.X (𝟙_ (Over (Sp K)))
      refine Finite.of_injective (fun t => (⟨e t.1, by rw [← map_pow, t.2, map_one]⟩ :
        {t : Multiplicative E.X →* Γ((𝟙_ (Over (Sp K))).left, ⊤)ˣ // t ^ n = 1})) ?_
      intro a b h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
  · intro Z π _ G _ _ _ w hw
    haveI : Finite (G.left.residueField w) :=
      (jacobson_closedPoints_tools_int G.left (G.hom ≫ π)).2.1 w hw
    let t₀ : Sp (G.left.residueField w) ⟶ Z := G.left.fromSpecResidueField w ≫ G.hom
    haveI := finite_points_over π G (G.left.residueField w) t₀
    let x₀ : Over.mk t₀ ⟶ G := Over.homMk (G.left.fromSpecResidueField w) rfl
    refine ⟨Nat.card (Over.mk t₀ ⟶ G), Nat.card_pos, fun K _ t x hx => ?_⟩
    obtain ⟨⟨z, φ⟩, hz⟩ := (Scheme.SpecToEquivOfField K G.left).symm.surjective x.left
    simp only [Scheme.SpecToEquivOfField_symm_apply] at hz
    obtain rfl : z = w := by
      have : x.left (default : Sp K) ∈ ({w} : Set G.left) := hx ▸ Set.mem_range_self _
      rw [← hz] at this
      have h2 : (Spec.map φ ≫ G.left.fromSpecResidueField z) (default : Sp K) ∈
          Set.range (G.left.fromSpecResidueField z) := ⟨_, rfl⟩
      rw [Scheme.range_fromSpecResidueField] at h2
      exact h2.symm.trans this
    let u : Over.mk t ⟶ Over.mk t₀ := Over.homMk (Spec.map φ) (by
      change Spec.map φ ≫ G.left.fromSpecResidueField z ≫ G.hom = t
      rw [← Category.assoc, hz]
      exact Over.w x)
    have hu : x = u ≫ x₀ := Over.OverMorphism.ext hz.symm
    rw [hu, ← comp_pow_points, pow_card_eq_one', MonObj.comp_one]

end GlobalTheory
end

