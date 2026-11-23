module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RosatiAdjPow
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.RosatiPower

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G]

private theorem padd_comp_eq_padd_comp_of_isMonHom {T H K : Over S} [GrpObj H] [GrpObj K] (q : H ⟶ K) [IsMonHom q]
    (a b : T ⟶ H) : padd H a b ≫ q = padd K (a ≫ q) (b ≫ q) := by
  unfold padd
  simp [IsMonHom.mul_hom]

private theorem comp_padd_eq_padd_comp {T T' H : Over S} [GrpObj H] (x : T ⟶ T') (a b : T' ⟶ H) :
    x ≫ padd H a b = padd H (x ≫ a) (x ≫ b) := by
  unfold padd
  first
  | simp
  | simp [Hom.mul_def]
  | simp [comp_lift_assoc]

theorem rosatiφ_comp (q : G' ⟶ G) [IsMonHom q] {f g : G ⟶ G} {f' g' : G' ⟶ G'}
    (hf : f' ≫ q = q ≫ f) (hg : g' ≫ q = q ≫ g) (k : Fin 6) :
    rosatiφ G' f' g' k ≫ q.left = (q ⊗ₘ q).left ≫ rosatiφ G f g k := by
  have e1 : (q ⊗ₘ q) ≫ fst G G = fst G' G' ≫ q := by simp
  have e2 : (q ⊗ₘ q) ≫ snd G G = snd G' G' ≫ q := by simp
  have key : ∀ (a : G' ⊗ G' ⟶ G') (b : G ⊗ G ⟶ G), a ≫ q = (q ⊗ₘ q) ≫ b →
      a.left ≫ q.left = (q ⊗ₘ q).left ≫ b.left := by
    intro a b h
    rw [← Over.comp_left, h, Over.comp_left]
  fin_cases k <;> refine key _ _ ?_ <;>
    simp only [padd_comp_eq_padd_comp_of_isMonHom, comp_padd_eq_padd_comp, Category.assoc, hf, hg, reassoc_of% e1, reassoc_of% e2, e1, e2]

theorem exists_restrict {A B : Over S} (q : A ⟶ B) (U : S.Opens) :
    ∃ n : (A.hom ⁻¹ᵁ U).toScheme ⟶ (B.hom ⁻¹ᵁ U).toScheme,
      n ≫ (B.hom ⁻¹ᵁ U).ι = (A.hom ⁻¹ᵁ U).ι ≫ q.left := by
  refine ⟨q.left.resLE (B.hom ⁻¹ᵁ U) (A.hom ⁻¹ᵁ U) ?_, Scheme.Hom.resLE_comp_ι _ _⟩
  intro x hx
  rw [← Over.w q] at hx
  exact hx

private theorem exists_isGen_of_isGen_iso_of_isGen {X : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB)
    (u : LB.Iso A B) (hu : u.IsGen) (t : LB.Gen B) (ht : t.IsGen) : ∃ t' : LB.Gen A, t'.IsGen := by
  classical
  let tS : LB.Sec B := ⟨fun b => (t.s b : Γ(X, B.U b)), fun i j => by
    have e := congrArg Units.val (ht i j)
    simpa [res] using e⟩
  have hunit : ∀ a, IsUnit ((secOfIso tS hu hA hB).f a) := by
    intro a
    apply RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace
    intro x hx
    have hc := cover_inf hB a hx
    rw [TopologicalSpace.Opens.mem_iSup] at hc
    obtain ⟨b, hb⟩ := hc
    have hsp := secOfIso_spec tS hu hA hB a b
    have e1 : X.presheaf.germ (A.U a) x hx ((secOfIso tS hu hA hB).f a) =
        X.presheaf.germ (A.U a ⊓ B.U b) x hb (rs inf_le_left ((secOfIso tS hu hA hB).f a)) := by
      simp only [rs, TopCat.Presheaf.germ_res_apply]
    change IsUnit (X.presheaf.germ (A.U a) x hx ((secOfIso tS hu hA hB).f a))
    rw [e1, hsp, isoCand, map_mul]
    refine IsUnit.mul ((Units.isUnit _).map _) ?_
    simp only [rs, TopCat.Presheaf.germ_res_apply]
    exact (Units.isUnit (t.s b)).map _
  refine ⟨⟨fun a => (hunit a).unit⟩, fun i j => ?_⟩
  apply Units.ext
  have e := (secOfIso tS hu hA hB).compat i j
  simpa [res] using e

end GlobalTheory.RosatiPower


open GlobalTheory.RosatiPower in
theorem GlobalTheory.rosatiAdj_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (boxLB L p.pr) → ∀ (f g : G ⟶ G) (f' g' : G' ⟶ G'), (∀ i, f' ≫ p.pr i = p.pr i ≫ f) → (∀ i, g' ≫ p.pr i = p.pr i ≫ g) → RosatiAdj G L f g → RosatiAdj G' L' f' g' := by
  intro S G' G _ _ _ _ j p L L' hL hL' hiso f g f' g' hf hg hr
  have hm : ∀ i, IsMonHom (p.pr i) := p.hom
  unfold RosatiAdj at hr ⊢
  unfold boxLB at hiso
  intro s
  obtain ⟨U, hsU, t, ht⟩ := hr s
  refine ⟨U, hsU, ?_⟩
  obtain ⟨w, hw⟩ := hiso
  have hn : ∀ i, ∃ n : ((G' ⊗ G').hom ⁻¹ᵁ U).toScheme ⟶ ((G ⊗ G).hom ⁻¹ᵁ U).toScheme,
      n ≫ ((G ⊗ G).hom ⁻¹ᵁ U).ι = ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ (p.pr i ⊗ₘ p.pr i).left :=
    fun i => exists_restrict (p.pr i ⊗ₘ p.pr i) U
  choose n hn using hn
  have hc : ∀ i k, (((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) ≫ (p.pr i).left =
      n i ≫ ((G ⊗ G).hom ⁻¹ᵁ U).ι ≫ rosatiφ G f g k := by
    intro i k
    rw [Category.assoc, rosatiφ_comp (p.pr i) (hf i) (hg i) k, ← Category.assoc, ← hn i, Category.assoc]
  let t' : ∀ i, ((L.pull (p.pr i).left).LinComb
      (fun k => ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) rosatiε).Gen :=
    fun i => GeneratorPullback.pullAlong L (p.pr i).left (n i) _ rosatiε _ (hc i) t
  have ht' : ∀ i, (t' i).IsGen := by
    intro i
    exact LBxP.isGen_pullAlong L (Over.Hom.left (p.pr i)) (n i) _ rosatiε _ (hc i) t ht
  have hb := GlobalTheory.BoxSymmetry.isGen_boxGen L (fun i => (p.pr i).left) _ rosatiε t' ht'
  have hwi := linCombIso_isGen w hw (fun k => ((G' ⊗ G').hom ⁻¹ᵁ U).ι ≫ rosatiφ G' f' g' k) rosatiε
  exact exists_isGen_of_isGen_iso_of_isGen (linComb_isLB _ hL' _ _) (linComb_isLB _ (linComb_isLB _ hL _ _) _ _) _ hwi _ hb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalOfPointwise
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxFamScalar

section Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y Y' W W' Z : Scheme.{0}}

theorem sval_of_secScal {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  unfold GeneratorPullback.SecScal resTop at H
  have hV : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have hW : h (r z) ∈ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hV.2 k
  have hc : LB.Coh L (Sum.elim φ₁ fun k => h ≫ φ₂ k)
      (Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k))) := by
    rintro (a | a) (b | b) e <;> simp only [Sum.elim_inl, Sum.elim_inr] at e ⊢ <;> rw [e]
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc]),
    sval_of s₁ r z J (fun k => J (r ≫ φ₁ k)) (fun k => rfl)]
  calc _ = _ := (gs_pull r h z _ hW _).symm
    _ = _ := (gs_res r z _ hV _).symm
    _ = _ := congrArg (gs r z _) (H _ _ hc)
    _ = _ := gs_mul r z _ hV _ _
    _ = _ := congrArg₂ (· * ·) (gs_res r z _ hV _) (gs_res r z _ hV _)

theorem secScal_of_pointwise {L : LB X} (hL : L.IsLB) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : ∀ (y : Y') (J : (Y' ⟶ X) → L.ι), Good L y J →
      sval s₂ (𝟙 Y' ≫ h) y J = gs (𝟙 Y') y ⊤ c * sval s₁ (𝟙 Y') y J) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c := by
  unfold GeneratorPullback.SecScal resTop
  intro j₁ j₂ hc
  apply fn_ext
  intro y hy
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL y (Sum.elim φ₁ fun k => h ≫ φ₂ k) (Sum.elim j₁ j₂) hc (by
    rintro (k | k)
    · exact Set.mem_iInter.1 hy.1 k
    · exact Set.mem_iInter.1 hy.2 k)
  have hW : h y ∈ LB.wchart L φ₂ j₂ := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
  have e := H y J hJ
  rw [sval_of s₂ (𝟙 Y' ≫ h) y J j₂ (fun k => by simpa using hJj (Sum.inr k)),
    sval_of s₁ (𝟙 Y') y J j₁ (fun k => by simpa using hJj (Sum.inl k))] at e
  calc _ = _ := gs_res _ y _ hy _
    _ = _ := gs_pull _ h y _ hW _
    _ = _ := e
    _ = _ := (congrArg₂ (· * ·) (gs_res _ y _ hy _) (gs_res _ y _ hy _)).symm
    _ = _ := (gs_mul _ y _ hy _ _).symm

variable {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem box_sval (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y' ⟶ Y)}
    (hφ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (s' : LB.Sec (LB.LinComb M' φ' ε))
    (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (hle : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι) i,
      LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM ≤
        ρ i ⁻¹ᵁ LB.wchart M (φ i) (fun a => jN a i))
    (H : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι),
      (@id (Γ(Y', LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
        ((LB.linCombIso w φ' ε).s (jN, jM))).val * rs inf_le_right (s'.f jM) =
        ∏ i, rs (hle jN jM i) (((ρ i).app _).hom ((s i).f (fun a => jN a i))))
    (q : Z ⟶ Y') (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (q ≫ φ' a) y (fun i => J ((q ≫ φ' a) ≫ pr i)) (J' (q ≫ φ' a)) ^ ε a).val * sval s' q y J' =
      ∏ i, sval (s i) (q ≫ ρ i) y J := by
  have hq : q y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) :=
    ⟨Good.mem (L := LB.LinComb M pr (fun _ => 1)) (J := fun ψ i => J (ψ ≫ pr i)) (fun ψ => hJ.mem pr ψ) φ' q,
      hJ'.mem φ' q⟩
  have key := congrArg (gs q y _) (H (fun a i => J ((q ≫ φ' a) ≫ pr i)) (fun a => J' (q ≫ φ' a)))
  calc _ = _ := congrArg (fun u => (∏ a, bw w (q ≫ φ' a) y (fun i => J ((q ≫ φ' a) ≫ pr i)) (J' (q ≫ φ' a)) ^ ε a).val * u)
          ((sval_of s' q y J' _ (fun a => rfl)).trans (gs_res q y _ hq _).symm)
    _ = _ := congrArg (· * _) (congrArg Units.val (gm_linCombIso w φ' ε q y _ _ hq).symm)
    _ = _ := congrArg (· * _) (gs_unit q y _ hq _).symm
    _ = _ := (gs_mul q y _ hq _ _).symm
    _ = _ := key
    _ = _ := gs_prod q y _ hq Finset.univ _
    _ = _ := Finset.prod_congr rfl fun i _ =>
          ((gs_res q y _ hq _).trans (gs_pull q (ρ i) y _ (hle _ _ i hq) _)).trans
            (sval_of (s i) (q ≫ ρ i) y J _ (fun a => by simp only [Category.assoc, hφ])).symm

theorem gs_scal {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  unfold scal
  have e := gs_pull (𝟙 Z) r z ⊤ trivial ((Scheme.Hom.appTop p).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c))
  rw [Category.id_comp] at e
  rw [← e, Scheme.Hom.comp_appTop]
  rfl

theorem gs_scal_prod {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (p' : Y' ⟶ Spec (CommRingCat.of R))
    (ρ : Fin j → (Y' ⟶ Y)) (hρ : ∀ i, ρ i ≫ p = p') (y : Y') (r : Fin j → R) :
    ∏ i, gs (𝟙 _ ≫ ρ i) y ⊤ (scal p (r i)) = gs (𝟙 _) y ⊤ (scal p' (∏ i, r i)) := by
  have hsc : (∏ i, scal p' (r i)) = scal p' (∏ i, r i) := by
    simp only [scal, map_prod]
  rw [← hsc, gs_prod (𝟙 _) y ⊤ trivial Finset.univ]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gs_scal, Category.id_comp, hρ]

theorem secScal_box (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    {K : Type} [Fintype K] {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X')} {φ : Fin j → K → (Y ⟶ X)} {ρ : Fin j → (Y' ⟶ Y)}
    {ψ' : K → (W' ⟶ X')} {ψ : Fin j → K → (W ⟶ X)} {σ : Fin j → (W' ⟶ W)}
    {h' : Y' ⟶ W'} {h : Y ⟶ W} (e' : ∀ a, φ' a = h' ≫ ψ' a) (e : ∀ i, h' ≫ σ i = ρ i ≫ h)
    (s' : LB.Sec (LB.LinComb M' φ' ε)) (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (t' : LB.Sec (LB.LinComb M' ψ' ε)) (t : ∀ i, LB.Sec (LB.LinComb M (ψ i) ε))
    (Hs : ∀ (y : Y') J J', Good M y J → Good M' y J' →
      (∏ a, bw w (𝟙 Y' ≫ φ' a) y (fun i => J ((𝟙 Y' ≫ φ' a) ≫ pr i)) (J' (𝟙 Y' ≫ φ' a)) ^ ε a).val *
        sval s' (𝟙 Y') y J' = ∏ i, sval (s i) (𝟙 Y' ≫ ρ i) y J)
    (Ht : ∀ (y : Y') J J', Good M y J → Good M' y J' →
      (∏ a, bw w (h' ≫ ψ' a) y (fun i => J ((h' ≫ ψ' a) ≫ pr i)) (J' (h' ≫ ψ' a)) ^ ε a).val *
        sval t' h' y J' = ∏ i, sval (t i) (h' ≫ σ i) y J)
    (c : Fin j → Γ(Y, ⊤)) (c' : Γ(Y', ⊤))
    (hc : ∀ y : Y', ∏ i, gs (𝟙 _ ≫ ρ i) y ⊤ (c i) = gs (𝟙 _) y ⊤ c')
    (H : ∀ i, GeneratorPullback.SecScal M (φ i) ε (s i) (ψ i) ε (t i) h (c i)) :
    GeneratorPullback.SecScal M' φ' ε s' ψ' ε t' h' c' := by
  apply secScal_of_pointwise hM'
  intro y J' hJ'
  obtain ⟨J, hJ, -⟩ := exists_good M hM y (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
  have hs := Hs y J J' hJ hJ'
  have ht := Ht y J J' hJ hJ'
  have hci := hc y
  have hH : ∀ i, sval (t i) (h' ≫ σ i) y J = gs (𝟙 Y' ≫ ρ i) y ⊤ (c i) * sval (s i) (𝟙 Y' ≫ ρ i) y J :=
    fun i => by rw [← sval_of_secScal (H i) (𝟙 Y' ≫ ρ i) y hJ, Category.id_comp, ← e i]
  simp only [Category.id_comp] at hs hH hci ⊢
  simp only [← e'] at ht
  refine (Units.isUnit (∏ a, bw w (φ' a) y (fun i => J (φ' a ≫ pr i)) (J' (φ' a)) ^ ε a)).mul_left_cancel ?_
  rw [ht, Finset.prod_congr rfl (fun i _ => hH i), Finset.prod_mul_distrib, hci, ← hs, mul_left_comm]

end Generic


set_option maxHeartbeats 800000 in
theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (pD : IsPowDeg D'.toPre D.toPre j) (k : ℕ) (Fs : Fin j → Fam D.toPre (FractionRing R) k) (f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α) (r : Fin j → R), (∀ i α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((Fs i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left (scal (DegPre.BF D.toPre (FractionRing R)).hom (r i))) → ∀ (F' : Fam D'.toPre (FractionRing R) k), IsBoxFam pD (FractionRing R) k F' Fs → ∀ α' : D'.toPre.X, GeneratorPullback.SecScal D'.toPre.P.L (DegPre.famφ D'.toPre (FractionRing R) α') (DegPre.famε k) (F'.s α') (D'.toPre.famφB α') (DegPre.famε k) (boxFamB pD k f α') (DegPre.prB D'.toPre (FractionRing R)).left (scal (DegPre.BF D'.toPre (FractionRing R)).hom (∏ i, r i)) := by
  intro R _ _ I j D D' pD k Fs f r hF F' hB α'
  have e1 : ∀ i, (D'.toPre.prB (FractionRing R)).left ≫ (pD.pw.pr i).left =
      prB pD (FractionRing R) i ≫ (D.toPre.prB (FractionRing R)).left := by
    intro i
    unfold prB DegPre.prB
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have e2 : ∀ i, prB pD (FractionRing R) i ≫ (D.toPre.BF (FractionRing R)).hom =
      (D'.toPre.BF (FractionRing R)).hom := fun i => Over.w (TF (FractionRing R) ◁ pD.pw.pr i)
  obtain ⟨hφ, hBα⟩ := hB α'
  obtain ⟨hφB, hBB⟩ := isBoxFamB_boxFamB pD k f α'
  exact secScal_box D.toPre.P.isLB D'.toPre.P.isLB pD.w
    (ρ := fun i => prB pD (FractionRing R) i) (σ := fun i => (pD.pw.pr i).left)
    (h' := (D'.toPre.prB (FractionRing R)).left) (h := (D.toPre.prB (FractionRing R)).left)
    (fun a => GC.famφ_eq D'.toPre (FractionRing R) α' a) e1
    (F'.s α') (fun i => (Fs i).s (pD.xe α' i)) (boxFamB pD k f α') (fun i => f i (pD.xe α' i))
    (fun y J J' hJ hJ' => box_sval pD.w hφ (F'.s α') _
      (fun jN _ i => inf_le_left.trans (box_le_of_comp _ _ _ _ _ i (hφ i) jN)) hBα (𝟙 _) y hJ hJ')
    (fun y J J' hJ hJ' => box_sval pD.w hφB (boxFamB pD k f α') _
      (fun jN _ i => inf_le_left.trans (box_le_of_comp _ _ _ _ _ i (hφB i) jN)) hBB _ y hJ hJ')
    (fun i => scal (D.toPre.BF (FractionRing R)).hom (r i)) _
    (fun y => gs_scal_prod _ _ _ e2 y r)
    (fun i => hF i (pD.xe α' i))

end GlobalTheory.BoxFamScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValFinProdGen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.QBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

def kap (ξ : Spec (CommRingCat.of (FractionRing V))) :
    FractionRing V →+* (Spec (CommRingCat.of (FractionRing V))).presheaf.stalk ξ :=
  ((Spec (CommRingCat.of (FractionRing V))).presheaf.germ ⊤ ξ trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom

omit [IsDiscreteValuationRing V] in
theorem gs_scal (ξ : Spec (CommRingCat.of (FractionRing V))) (c : FractionRing V) :
    gs (𝟙 _) ξ ⊤ (scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c) = kap ξ c := by
  rw [gs_eq _ ξ ⊤ trivial]
  rfl

def SV (ϖ : V) (ξ : Spec (CommRingCat.of (FractionRing V)))
    (s : ((Spec (CommRingCat.of (FractionRing V))).presheaf.stalk ξ)ˣ) (n : ℤ) : Prop :=
  ∃ c, HasVal ϖ c n ∧ s.val = kap ξ c

theorem SV.mul (hϖ : Irreducible ϖ) {ξ : Spec (CommRingCat.of (FractionRing V))} {s t} {n m : ℤ}
    (hs : SV ϖ ξ s n) (ht : SV ϖ ξ t m) : SV ϖ ξ (s * t) (n + m) := by
  obtain ⟨c, ⟨u, hu⟩, hc⟩ := hs
  obtain ⟨d, ⟨v, hv⟩, hd⟩ := ht
  refine ⟨c * d, ⟨u * v, ?_⟩, by rw [Units.val_mul, hc, hd, map_mul]⟩
  rw [hu, hv, zpow_add₀ ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2
      hϖ.ne_zero), Units.val_mul, map_mul]; ring

theorem SV.prod (hϖ : Irreducible ϖ) {ξ : Spec (CommRingCat.of (FractionRing V))} {T : Type} (S : Finset T)
    {s : T → _} {n : T → ℤ} (hs : ∀ i, SV ϖ ξ (s i) (n i)) : SV ϖ ξ (∏ i ∈ S, s i) (∑ i ∈ S, n i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, ⟨1, by simp⟩, by simp⟩
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha]; exact (hs a).mul hϖ ih

theorem SV.unique (hϖ : Irreducible ϖ) {ξ : Spec (CommRingCat.of (FractionRing V))} {s} {n m : ℤ}
    (hs : SV ϖ ξ s n) (ht : SV ϖ ξ s m) : n = m := by
  obtain ⟨c, hc, e⟩ := hs
  obtain ⟨d, hd, e'⟩ := ht
  have : c = d := (kap ξ).injective (e.symm.trans e')
  exact hasVal_unique hϖ hc (this ▸ hd)

theorem sv_unit (ξ : Spec (CommRingCat.of (FractionRing V))) (U : (Spec (CommRingCat.of V)).Opens)
    (hU : (closedPoint V : Spec (CommRingCat.of V)) ∈ U) (a : Γ(Spec (CommRingCat.of V), U)ˣ) :
    SV ϖ ξ (gm (jK V) ξ U a) 0 := by
  obtain rfl := eq_top_of_closedPoint_mem U hU
  refine ⟨algebraMap V _ ((Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom a : Vˣ) : V),
    ⟨_, by rw [zpow_zero, _root_.one_mul]⟩, ?_⟩
  rw [gm_val _ ξ ⊤ trivial]
  have hnat := congrArg (fun f => (CommRingCat.Hom.hom f) ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a.val))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  refine congrArg ((Spec (CommRingCat.of (FractionRing V))).presheaf.germ ⊤ ξ trivial).hom
    (Eq.trans ?_ hnat.symm)
  rw [Iso.hom_inv_id_apply]
  rfl

theorem sv_unit' (ξ : Spec (CommRingCat.of (FractionRing V))) {X : Scheme.{0}} (p : Spec (CommRingCat.of V) ⟶ X)
    (U : X.Opens) (hU : p (closedPoint V) ∈ U) (a : Γ(X, U)ˣ) :
    SV ϖ ξ (gm (jK V ≫ p) ξ U a) 0 := by
  have h : p (jK V ξ) ∈ U := by
    have := eq_top_of_closedPoint_mem (p ⁻¹ᵁ U) hU
    have h2 : jK V ξ ∈ p ⁻¹ᵁ U := by rw [this]; trivial
    exact h2
  rw [← gm_pull (jK V) p ξ U h]
  exact sv_unit ξ _ hU _

theorem sv_gen (hϖ : Irreducible ϖ) (ξ : Spec (CommRingCat.of (FractionRing V))) {X : Scheme.{0}} {L : LB X}
    {Ix : Type} [Fintype Ix]
    {φ : Ix → (Spec (CommRingCat.of V) ⟶ X)} {φ' : Ix → (Spec (CommRingCat.of (FractionRing V)) ⟶ X)}
    {hφ : ∀ k, φ' k = jK V ≫ φ k} {ε : Ix → ℤ} {t : LB.Gen (LB.LinComb L φ' ε)} {n : ℤ}
    (hn : GenHasVal ϖ L φ φ' hφ ε t n) {J} (hJ : Good L ξ J)
    (hc : ∀ k, φ k (closedPoint V) ∈ L.U (J (jK V ≫ φ k))) : SV ϖ ξ (val t (𝟙 _) ξ J) n := by
  obtain ⟨e, c, -, hcv, H⟩ := SectionScalarValuation.exists_val_genHasVal hn
  have H1 := H _ (𝟙 _) ξ J hJ
  rw [gs_scal, Category.id_comp] at H1
  obtain ⟨d, ⟨u, hu⟩, hd⟩ : SV ϖ ξ (val e (jK V) ξ J) 0 :=
    sv_unit ξ _ (Set.mem_iInter.2 hc) _
  refine ⟨c * d, ?_, by rw [H1, hd, map_mul]⟩
  rw [hu, zpow_zero, _root_.one_mul]
  exact hasVal_mul_unit hcv u

theorem exists_goodV (ξ : Spec (CommRingCat.of (FractionRing V))) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (s : X ⟶ Spec (CommRingCat.of V)) [IsSeparated s] :
    ∃ J, Good L ξ J ∧ ∀ p : Spec (CommRingCat.of V) ⟶ X, p ≫ s = 𝟙 _ →
      p (closedPoint V) ∈ L.U (J (jK V ≫ p)) := by
  haveI : IsDominant (jK V) := isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of V) ⟶ X => exists_chart hL (p (closedPoint V))
  obtain ⟨J, hJ, e⟩ := exists_good L hL ξ (K := {p : Spec (CommRingCat.of V) ⟶ X // p ≫ s = 𝟙 _})
    (fun p => jK V ≫ p.1) (fun p => pick p.1)
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated s (a.2.trans b.2.symm) (jK V) h))
    (fun p => by
      have := eq_top_of_closedPoint_mem (p.1 ⁻¹ᵁ L.U (pick p.1)) (hpk p.1)
      have h2 : jK V ξ ∈ p.1 ⁻¹ᵁ L.U (pick p.1) := by rw [this]; trivial
      exact h2)
  exact ⟨J, hJ, fun p hp => (e ⟨p, hp⟩).symm ▸ hpk p⟩

section Box

variable {X X' Y : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem mapsAt_val (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb M' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => p ≫ pr i) (fun _ => n)))
    (H : GeneratorPullback.MapsAt M M' pr w p n a b) (y : Y) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    val b (𝟙 _) y J = bw w p y (fun i => J (p ≫ pr i)) (J' p) ^ n * val a (𝟙 _) y J' := by
  have hm' : p y ∈ LB.wchart M pr (fun i => J (p ≫ pr i)) ⊓ M'.U (J' p) :=
    ⟨Set.mem_iInter.2 fun i => hJ (p ≫ pr i), hJ' p⟩
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ p ⁻¹ᵁ (LB.div (LB.LinComb M pr (fun _ => 1)) M').U (fun i => J (p ≫ pr i), J' p) := hm'
  have E := congrArg (gm (𝟙 Y) y _) (H (fun i => J (p ≫ pr i)) (J' p))
  rw [val_of b _ y J (fun i => J (p ≫ pr i)) (fun i => by rw [Category.id_comp]),
    val_of a _ y J' (fun _ => J' p) (fun i => by rw [Category.id_comp])]
  refine (gm_res _ y _ hm _).symm.trans (E.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ n) ?_)) (gm_res _ y _ hm _))))
  exact gm_pull (𝟙 Y) p y _ hm' _

theorem val_finProdGen {K I : Type} [Fintype K] [Fintype I] (φ : I → K → (Y ⟶ X)) (ε : I → K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) (ε i))) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good M z J) :
    val (GeneratorPullback.finProdGen M φ ε t) r z J = ∏ i, val (t i) r z J :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
    gm_res r z _ (hJ.mem (fun p : I × K => φ p.1 p.2) r) _)

end Box

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → QForm.IsQ D'.toPre ϖ (fun x => ∑ i, Q (pD.xe x i)) := by
  intro V _ _ _ ϖ hϖ j D D' pD Q hQ x
  obtain ⟨m, hm⟩ := QForm.exists_QVal hϖ D' x
  suffices h : m = ∑ i, Q (pD.xe x i) by rw [h] at hm; exact hm
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing V))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_goodV ξ D.toPre.P.isLB D.toPre.P.A.hom
  obtain ⟨J', hJ', hJc'⟩ := exists_goodV ξ D'.toPre.P.isLB D'.toPre.P.A.hom
  obtain ⟨b, hb, hcorr⟩ := pD.w_psi x
  have e1 := mapsAt_val pD.w _ _ _ b hb ξ hJ hJ'
  have e2 := (val_corr hJ hcorr (𝟙 _)).trans (val_finProdGen _ _ _ _ _ hJ)
  have s1 : SV ϖ ξ (val (D'.toPre.psi x) (𝟙 _) ξ J') m :=
    sv_gen hϖ ξ hm hJ' fun _ => hJc' _ (Over.w _)
  have s2 := SV.prod hϖ Finset.univ fun i : Fin j =>
    sv_gen hϖ ξ (hQ (pD.xe x i)) hJ fun _ => hJc _ (Over.w _)
  have hx : D'.toPre.xK x = jK V ≫ (D'.toPre.c x).left := QForm.ptK_eq _ x
  have s3 : SV ϖ ξ (bw pD.w (D'.toPre.xK x) ξ (fun i => J (D'.toPre.xK x ≫ (pD.pw.pr i).left))
      (J' (D'.toPre.xK x))) 0 := by
    rw [hx]
    refine sv_unit' ξ _ _ ?_ _
    refine ⟨Set.mem_iInter.2 fun i => ?_, hJc' _ (Over.w _)⟩
    exact hJc ((D'.toPre.c x).left ≫ (pD.pw.pr i).left) (QForm.over_sec _ _)
  have s4 := s3.mul hϖ s2
  rw [← e2, zero_add] at s4
  have e3 := e1
  rw [zpow_neg_one, eq_inv_mul_iff_mul_eq] at e3
  exact s1.unique hϖ (e3 ▸ s4)

end GlobalTheory.QBox
end
end

