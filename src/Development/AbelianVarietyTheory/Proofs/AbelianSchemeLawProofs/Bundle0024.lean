module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CompAutEqOfSerreBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem comp_aut_eq_of_serre_baseChange (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S)
    (P : PolAV S) (M : ℕ)
    (hS' : ∀ (P : PolAV S') (σ : P.A ≅ P.A), IsMonHom σ.hom →
      (∃ c : LB.Gen (LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]), c.IsGen) →
      (∀ (T : Over S') (x : T ⟶ P.A), x ^ M = 1 → x ≫ σ.hom = x) → σ.hom = 𝟙 P.A)
    (σ : P.A ≅ P.A) (hσ : IsMonHom σ.hom) (V : S.Opens) (hV : ∀ y, f y ∈ V)
    (c : LB.Gen ((LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]).pull
      (P.A.hom ⁻¹ᵁ V).ι)) (hc : c.IsGen)
    (hfix : ∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ σ.hom = x) :
    ∃ (X : Scheme.{0}) (g : X ⟶ P.A.left) (q : X ⟶ S'), IsPullback g q P.A.hom f ∧
      g ≫ σ.hom.left = g := by
  obtain ⟨P', g, hg, -, pm, hw⟩ := hB S S' f P
  have inj : ∀ {T : Over S'} {x y : T ⟶ P'.A}, toBase hg.w x = toBase hg.w y → x = y :=
    fun {T x y} h => Over.OverMorphism.ext
      (hg.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act : (P.A ⟶ P.A) → (P'.A ⟶ P'.A) := fun a => Over.homMk (hg.lift (g ≫ a.left) P'.A.hom
    (by rw [Category.assoc, Over.w, hg.w])) (hg.lift_snd _ _ _)
  have ha : ∀ a, (act a).left ≫ g = g ≫ a.left := fun a => hg.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ P'.A) a, toBase hg.w (x ≫ act a) = toBase hg.w x ≫ a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have cancel : ∀ a b : P.A ⟶ P.A, a ≫ b = 𝟙 _ → act a ≫ act b = 𝟙 _ := fun a b e => inj (by
    rw [pa, ← Category.id_comp (act a), pa, Category.assoc, e, Category.comp_id])
  let σ' : P'.A ≅ P'.A := ⟨act σ.hom, act σ.inv, cancel _ _ σ.hom_inv_id, cancel _ _ σ.inv_hom_id⟩
  obtain ⟨w, gw'⟩ := LBIso.symm (A := P.L.pull g) (B := P'.L) hw
  have key : σ'.hom = 𝟙 P'.A := by
    refine hS' P' σ' (isMonHom_of_mul _ fun T x y => inj ?_) ?_ fun T x hx => inj ?_
    · rw [pm]
      show toBase hg.w ((x * y) ≫ act σ.hom) =
        toBase hg.w (x ≫ act σ.hom) * toBase hg.w (y ≫ act σ.hom)
      rw [pa, pa, pa, pm, MonObj.mul_comp]
    · obtain ⟨n, hn⟩ : ∃ n : P'.A.left ⟶ (P.A.hom ⁻¹ᵁ V).toScheme, n ≫ (P.A.hom ⁻¹ᵁ V).ι = g :=
        ⟨IsOpenImmersion.lift _ g (by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          exact (congrArg (fun q => q y ∈ V) hg.w).mpr (hV _)), IsOpenImmersion.lift_fac _ _ _⟩
      obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn P.L _ _ _) c hc
      obtain ⟨a, h₂, -⟩ := H1.exists_gen_move P.isLB P'.isLB w ((isGen_iff w).1 gw') (K := Fin 2) _
        ![σ'.hom.left, 𝟙 P'.A.left] _ n (fun k => by
          rw [← Category.assoc, hn]
          fin_cases k
          · exact ha σ.hom
          · exact (Category.id_comp _).trans (Category.comp_id _).symm) c₁ h₁
      exact ⟨a, h₂⟩
    · let ρ : (T ⟶ P'.A) →* (Over.mk (T.hom ≫ f) ⟶ P.A) := MonoidHom.mk' (toBase hg.w) (pm T)
      have h₁ : toBase hg.w x ^ M = 1 := (map_pow ρ x M).symm.trans (by rw [hx, map_one])
      exact (pa x σ.hom).trans (hfix _ _ h₁)
  refine ⟨_, g, _, hg, (ha σ.hom).symm.trans ?_⟩
  show σ'.hom.left ≫ g = g
  rw [key, Over.id_left, Category.id_comp]

theorem serre_of_algClosed : PolBaseChangeSt → GlobalFnsSt → (∀ (X T Y : Scheme.{0}) (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y), ε ≫ p = 𝟙 T → UniversallyClosed p → (∀ V : T.Opens, Function.Surjective (p.app V).hom) → ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) → ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : ℕ), 3 ≤ M → ∀ σ : P.A ≅ P.A, IsMonHom σ.hom → (∃ c : LB.Gen (LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]), c.IsGen) → (∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ P.A), x ^ M = 1 → x ≫ σ.hom = x) → σ.hom = 𝟙 P.A) → SerreSt := by
  intro hB hG hR hK S _ P M hM σ hσ hloc hfix
  have := P.isAb.proper
  let u : P.A ⟶ P.A := σ.hom * (𝟙 P.A)⁻¹
  have hu : ∀ {T : Over S} (x : T ⟶ P.A), x ≫ σ.hom = x → x ≫ u = 1 := fun x hx => by
    simp only [u, MonObj.comp_mul, GrpObj.comp_inv, hx, Category.comp_id, mul_inv_cancel]
  have hη : (η[P.A] : 𝟙_ (Over S) ⟶ P.A).left ≫ P.A.hom = 𝟙 S := Over.w η[P.A]
  have hfib : ∀ (t : S) (x : P.A.left), P.A.hom x = t →
      u.left x = (η[P.A] : 𝟙_ (Over S) ⟶ P.A).left t := by
    intro t x hx
    let K : Type := AlgebraicClosure (S.residueField t)
    let f : Spec (CommRingCat.of K) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField t) K)) ≫ S.fromSpecResidueField t
    have hf : ∀ y, f y = t := fun y =>
      (Scheme.Hom.comp_apply _ _ y).trans (Scheme.fromSpecResidueField_apply t _)
    obtain ⟨V, hV, c, hc⟩ := hloc t
    obtain ⟨X, g, q, hg, e⟩ := comp_aut_eq_of_serre_baseChange hB f P M (fun P' => hK K P' M hM)
      σ hσ V (fun y => by rw [hf]; exact hV) c hc hfix
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hg x (default : PrimeSpectrum K)
      (hx.trans (hf _).symm)
    let x₀ : Over.mk (g ≫ P.A.hom) ⟶ P.A := Over.homMk g rfl
    have h₀ : g ≫ u.left = (g ≫ P.A.hom) ≫ (η[P.A] : 𝟙_ (Over S) ⟶ P.A).left :=
      congrArg (fun q => q.left) (hu x₀ (Over.OverMorphism.ext e))
    rw [← Scheme.Hom.comp_apply, h₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]
  have key : u.left = P.A.hom ≫ (η[P.A] : 𝟙_ (Over S) ⟶ P.A).left ≫ u.left := by
    refine Scheme.hom_ext_of_forall _ _ fun x => ?_
    obtain ⟨V, hV, e⟩ := hR _ _ _ P.A.hom _ u.left hη inferInstance
      (surjective_app_of_isAbelianScheme hG P.A P.isAb) (P.A.hom x) _ (hfib _)
    exact ⟨P.A.hom ⁻¹ᵁ V, hV, e⟩
  have h₁ : u = toUnit P.A ≫ η[P.A] ≫ u := Over.OverMorphism.ext key
  rw [hu η[P.A] (IsMonHom.one_hom σ.hom), MonObj.comp_one] at h₁
  exact mul_inv_eq_one.1 h₁

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbSquare

theorem exists_gen_of_mem_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i : K → L.ι) (hi : ∀ k (y : Y), φ k y ∈ L.U (i k)) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have hm : ∀ y : Y, y ∈ LB.wchart L φ i := fun y => Set.mem_iInter.2 fun k => hi k y
  have le : ∀ j : K → L.ι, LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ i :=
    fun j y hy => ⟨hy, hm y⟩
  have v : ∀ (j : K → L.ι) (y : Y), y ∈ LB.wchart L φ j →
      gm (𝟙 Y) y (LB.wchart L φ j) (res (le j) ((LB.LinComb L φ ε).g j i)) = trF φ ε (𝟙 Y) y j i :=
    fun j y hy => (gm_res (𝟙 Y) y (le j) hy _).trans (gm_linComb L φ ε (𝟙 Y) y j i hy (hm y))
  refine ⟨⟨fun j => res (le j) ((LB.LinComb L φ ε).g j i)⟩, fun j j' => unit_ext fun y hy => ?_⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j y hy.1)).trans (Eq.symm ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2)
      ((gm_res (𝟙 Y) y _ hy _).trans (v j' y hy.2))).trans ?_)))
  exact trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hm y)

theorem exists_gen_square {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    (hL : L.IsLB) (t : LB.Gen (Theta G L)) (ht : t.IsGen) {T : Over S} (a b c : T ⟶ G) (i : Fin 4 → L.ι)
    (hi : ∀ k (y : T.left), (![(a * b).left, a.left, b.left, (1 : T ⟶ G).left] k) y ∈ L.U (i k)) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 4) ![(a * b * c).left, c.left, (a * c).left, (b * c).left]
      ![1, 1, -1, -1]), u.IsGen := by
  obtain ⟨w, hw⟩ := exists_gen_of_mem_chart hL _ ![1, -1, -1, 1] i hi
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := ![(a * b * c).left, c.left, (a * c).left, (b * c).left])
    (ε' := ![1, 1, -1, -1]) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl (prod_cub a b c h))).trans ?_
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L _ _ _ _ w (LB.pullGen L (thφ G (x3 G)) thε t (lift a (lift b c)).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw (DVR.pullGen_isGen _ _ _ _ ht _))
  exact ⟨u, hu⟩

theorem square_local {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    (hL : L.IsLB) (t : LB.Gen (Theta G L)) (ht : t.IsGen) (T : Over S) (x y : T ⟶ G) (p : T.left) :
    ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb L (K := Fin 4)
      ![(translPt G (x * y)).left, (snd T G).left, (translPt G x).left, (translPt G y).left]
      ![1, 1, -1, -1]).pull ((fst T G).left ⁻¹ᵁ V).ι), c.IsGen := by
  let χ : Fin 4 → (T.left ⟶ G.left) := ![(x * y).left, x.left, y.left, (1 : T ⟶ G).left]
  choose i hi using fun k => exists_chart hL (χ k p)
  refine ⟨LB.wchart L χ i, Set.mem_iInter.2 hi, ?_⟩
  let W := (fst T G).left ⁻¹ᵁ LB.wchart L χ i
  let ρ : overRes (T := T ⊗ G) W ⟶ T ⊗ G := overResι W
  have e : ∀ k, (![((ρ ≫ fst T G ≫ x) * (ρ ≫ fst T G ≫ y)).left, (ρ ≫ fst T G ≫ x).left,
      (ρ ≫ fst T G ≫ y).left, (1 : overRes (T := T ⊗ G) W ⟶ G).left] k) = W.ι ≫ (fst T G).left ≫ χ k := by
    intro k
    fin_cases k
    · show _ = (ρ ≫ fst T G ≫ (x * y)).left
      rw [MonObj.comp_mul, MonObj.comp_mul]; rfl
    · rfl
    · rfl
    · show _ = (ρ ≫ fst T G ≫ (1 : T ⟶ G)).left
      rw [MonObj.comp_one, MonObj.comp_one]; rfl
  obtain ⟨u, hu⟩ := exists_gen_square hL t ht (ρ ≫ fst T G ≫ x) (ρ ≫ fst T G ≫ y) (ρ ≫ snd T G) i
    (fun k z => by
      rw [e k]
      exact Set.mem_iInter.1 z.2 k)
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) u hu
  have tr : ∀ w : T ⟶ G, (ρ ≫ fst T G ≫ w) * (ρ ≫ snd T G) = ρ ≫ translPt G w := fun w =>
    (MonObj.comp_mul ρ (fst T G ≫ w) (snd T G)).symm
  fin_cases k
  · show _ = (ρ ≫ translPt G (x * y)).left
    rw [← tr, MonObj.comp_mul, MonObj.comp_mul]; rfl
  · rfl
  · exact congrArg (fun q => q.left) (tr x)
  · exact congrArg (fun q => q.left) (tr y)

theorem square_of_cube :
    (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) →
    (∀ (S : Scheme.{0}) (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left),
      ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4)
        ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left, (translPt P.A y).left]
        ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) ∧ SquareSt := by
  intro h
  have key : ∀ (S : Scheme.{0}) (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left),
      ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4)
        ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left, (translPt P.A y).left]
        ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen := by
    intro S P T x y p
    obtain ⟨t, ht⟩ := h S P P.L P.isLB
    exact square_local P.isLB t ht T x y p
  exact ⟨key, fun S _ P T x y p => key S P T x y p⟩

end GlobalTheory.AbSquare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolBaseChange

theorem lbIso_refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {L : LB A.left}

theorem eSec_comm (h : IsGrpPullback A' A f φ) : eSec A' ≫ φ = f ≫ eSec A := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ A') = η[A'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[A]).left = _
  simp [eSec]

theorem inv_comm (h : IsGrpPullback A' A f φ) :
    (GrpObj.inv : A' ⟶ A').left ≫ φ = φ ≫ (GrpObj.inv : A ⟶ A).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h A') (𝟙 A'))
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  refine e.trans ?_
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem rigidified_pull (h : IsGrpPullback A' A f φ) (hr : Rigidified A L) : Rigidified A' (L.pull φ) := by
  obtain ⟨t, ht⟩ := hr
  exact gen_chartPull (chartPullLinComb L φ (fun _ : PUnit => eSec A') (fun _ => eSec A) (fun _ => 1) f
    fun _ => eSec_comm h) t ht

theorem sym_pull (h : IsGrpPullback A' A f φ) (hs : Sym A L) : Sym A' (L.pull φ) := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := hs (f s)
  refine ⟨f ⁻¹ᵁ U, hU, ?_⟩
  have le' : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy =>
    (congrArg (fun q => q y ∈ U) h.1.w).mpr hy
  have hψ : φ.resLE _ _ le' ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  refine gen_chartPull (chartPullLinComb L φ _ _ _ (φ.resLE _ _ le') fun k => ?_) t ht
  fin_cases k
  · show (_ ≫ _) ≫ φ = _ ≫ _ ≫ _
    rw [Category.assoc, inv_comm h, ← Category.assoc, ← hψ, Category.assoc]
  · exact hψ.symm


omit [GrpObj A] [GrpObj A'] in
theorem relAmple_restrict (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hA : RelAmple A L)
    (V : S.Opens) (hV : IsAffineOpen V) :
    RelAmple (Over.mk (A'.hom ∣_ (f ⁻¹ᵁ V))) ((L.pull φ).pull (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) := by
  have H : IsPullback ((A'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (A'.hom ∣_ (f ⁻¹ᵁ V)) A.hom ((f ⁻¹ᵁ V).ι ≫ f) :=
    (isPullback_morphismRestrict A'.hom (f ⁻¹ᵁ V)).flip.paste_horiz h
  obtain ⟨w, hw⟩ : LBIso ((L.pull φ).pull (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) (L.pull ((A'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ)) :=
    LBIso.chartPull (chartPullLinComb L φ (fun _ : PUnit => (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι)
      (fun _ => (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (lbIso_refl (LB.isLB_pull hL _))
  exact relAmple_pull (A' := Over.mk (A'.hom ∣_ (f ⁻¹ᵁ V))) H hL (LB.isLB_pull (LB.isLB_pull hL _) _)
    ((isGen_iff w).1 hw) V hV (fun y => y.2) hA

end GlobalTheory.PolBaseChange

namespace GlobalTheory

open PolBaseChange

theorem polBaseChange_of_relAmple_local :
    (∀ (S : Scheme.{0}) (A : Over S) (L : LB A.left), L.IsLB → QuasiCompact A.hom → QuasiSeparated A.hom →
      (∀ s : S, ∃ (U : S.Opens) (_ : s ∈ U), RelAmple (Over.mk (A.hom ∣_ U)) (L.pull (A.hom ⁻¹ᵁ U).ι)) →
      RelAmple A L) → PolBaseChangeSt := by
  intro hloc S S' f P
  have h := isGrpPullback_pullback P.A f
  have hab := TLinPf.isAb_pullback f P.A P.isAb
  have hL' := LB.isLB_pull P.isLB (pullback.fst P.A.hom f)
  obtain ⟨w, hw⟩ := lbIso_refl hL'
  have := hab.proper
  have hamp : RelAmple ((Over.pullback f).obj P.A) (P.L.pull (pullback.fst P.A.hom f)) := by
    refine hloc S' _ _ hL' inferInstance inferInstance fun s => ?_
    obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f s) trivial
    exact ⟨f ⁻¹ᵁ V, hs, relAmple_restrict h.1 P.isLB P.ample V hV⟩
  refine ⟨{ A := (Over.pullback f).obj P.A
            isAb := hab
            g := P.g
            smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
            L := P.L.pull (pullback.fst P.A.hom f)
            isLB := hL'
            rigid := rigidified_pull h P.rigid
            sym := sym_pull h P.sym
            ample := hamp
            ktriv := kTriv_pull h P.isLB hL' ((isGen_iff w).1 hw) P.ktriv },
    pullback.fst P.A.hom f, h.1, rfl, fun T x y => ?_, w, hw⟩
  exact Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

def chartPullPw {X : Scheme.{0}} (H : LB X) (N : ℕ) :
    ChartPull (pw H N) (LB.LinComb H (K := Fin N) (fun _ => 𝟙 X) (fun _ => 1)) (𝟙 X) :=
  have le : ∀ i : H.ι, H.U i ≤ LB.wchart H (K := Fin N) (fun _ => 𝟙 X) (fun _ => i) :=
    fun _ _ hy => Set.mem_iInter.2 fun _ => hy
  { idx := fun i _ => i
    le := le
    g := fun y i j hi hj => by
      refine Eq.trans ?_ (gm_linComb H (K := Fin N) (fun _ => 𝟙 X) (fun _ => 1) (𝟙 X) y _ _
        (le i hi) (le j hj)).symm
      refine (map_zpow (gm (𝟙 X) y (H.U i ⊓ H.U j)) (H.g i j) (N : ℤ)).trans ?_
      simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, zpow_natCast,
        Category.id_comp] }

theorem veryAmpleBy_of_relAmple {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))}
    {L : LB A.left} (hL : L.IsLB) (hA : RelAmple A L) {X : Scheme.{0}} (e : X ⟶ A.left) [IsIso e]
    {f : X ⟶ Spec (CommRingCat.of R)} (hf : e ≫ A.hom = f) {H : LB X} (hH : H.IsLB)
    (hw : LBIso H (L.pull e)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw H N)),
      (pw H N).IsLB ∧ VeryAmpleBy f (pw H N) s := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA ⊤ (isAffineOpen_top _)
  have : IsIso (A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso A.left.topIso.hom)
  obtain ⟨ψ, hiso, hψ⟩ : ∃ ψ : X ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme, IsIso ψ ∧ ψ ≫ (A.hom ⁻¹ᵁ ⊤).ι = e :=
    ⟨e ≫ inv (A.hom ⁻¹ᵁ ⊤).ι, inferInstance, by simp⟩
  have hP := linComb_isLB L hL (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1)
  have hP' := isLB_pw hH N
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullPw H N)
    (chartPullOut L (fun _ : Fin N => (A.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1) ψ _
      fun _ => (Category.id_comp _).trans hψ.symm)
    (iso_linComb ((isGen_iff w).1 hw) (fun _ : Fin N => 𝟙 X) (fun _ => 1))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hP' (s i)
  have loc : ∀ i, nonzeroLocus (M := pw H N) (s' i) = ψ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1
        ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨N, hN, M, s', hP', ?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show ψ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (ψ y)
    have hm : ψ y ∈ nonzeroLocus (s i) ⊓ (powOver A L ⊤ N).U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · have hT : IsIso (⊤ : (Spec (CommRingCat.of R)).Opens).ι :=
      inferInstanceAs (IsIso (Spec (CommRingCat.of R)).topIso.hom)
    let θ : CommRingCat.of R ⟶ Γ((⊤ : (Spec (CommRingCat.of R)).Opens).toScheme, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (⊤ : (Spec (CommRingCat.of R)).Opens).ι.app ⊤
    have hθi : IsIso θ := IsIso.comp_isIso' inferInstance (inferInstanceAs
      (IsIso ((⊤ : (Spec (CommRingCat.of R)).Opens).ι.app ⊤)))
    have hθ : Function.Surjective θ.hom :=
      (ConcreteCategory.bijective_of_isIso θ).2
    have hf' : f = ψ ≫ (A.hom ∣_ ⊤) ≫ (⊤ : (Spec (CommRingCat.of R)).Opens).ι := by
      rw [morphismRestrict_ι, ← Category.assoc, hψ, hf]
    have hap : IsIso (ψ.appLE _ _ (loc i).le) := by
      have key : ∀ (V : X.Opens) (h : V = ψ ⁻¹ᵁ nonzeroLocus (s i)), IsIso (ψ.appLE _ V h.le) := by
        rintro _ rfl
        rw [Scheme.Hom.appLE_eq_app]
        infer_instance
      exact key _ (loc i)
    have hc : cst f (nonzeroLocus (M := pw H N) (s' i)) =
        (ψ.appLE _ _ (loc i).le).hom.comp
          (((A.hom ∣_ ⊤).appLE ⊤ (nonzeroLocus (s i)) le_top).hom.comp θ.hom) := by
      rw [hf']
      have e₁ := Scheme.Hom.appLE_comp_appLE ψ (A.hom ∣_ ⊤) ⊤ (nonzeroLocus (s i))
        (nonzeroLocus (M := pw H N) (s' i)) le_top (loc i).le
      ext x
      have e₂ := congrArg (fun q => q.hom (θ.hom x)) e₁
      exact e₂.symm
    intro d
    obtain ⟨d, rfl⟩ := (ConcreteCategory.bijective_of_isIso (ψ.appLE _ _ (loc i).le)).2 d
    obtain ⟨p, rfl⟩ := hsurj d
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective θ.hom hθ p
    refine ⟨p, ?_⟩
    rw [hc, MvPolynomial.eval₂Hom_map_hom]
    exact (MvPolynomial.map_eval₂Hom _ _ _ p).symm

theorem polAV_veryAmpleBy : PolBaseChangeSt → ∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s := by
  intro hBC S P R _ t X π f h
  obtain ⟨P', g, hg, -, -, w⟩ := hBC S _ t P
  let e := h.isoIsPullback _ _ hg
  have he : e.hom ≫ g = π := h.isoIsPullback_hom_fst _ _ hg
  exact veryAmpleBy_of_relAmple P'.isLB P'.ample e.hom (h.isoIsPullback_hom_snd _ _ hg)
    (pull_isLB P.isLB π)
    (LBIso.chartPull (chartPullSame P.L (fun _ : PUnit => π) (fun _ => g) (fun _ => 1) e.hom fun _ => he.symm)
      (chartPullPull P'.L e.hom e.hom rfl) w)

end GlobalTheory.AbLaw
end
end

