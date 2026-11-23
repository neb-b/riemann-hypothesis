module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwoModelsCommonCoverCompare

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetSectionValueOnChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem exists_unitΓ_eq {A : Type} [CommRing A] (u : Γ(Sp A, ⊤)ˣ) : ∃ e : Aˣ, unitΓ e = u := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom u, Units.ext ?_⟩
  exact congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id

theorem val_eq_unit_of_red : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (B : Type) [CommRing B] (p : ℕ) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp (Jet B Unit p) ⟶ Y) (j₀ : L.ι), (∀ κ q, (r ≫ φ κ) q ∈ L.U j₀) → (∀ (z' : Sp B) (J' : (Sp B ⟶ X) → L.ι), Good L z' J' → (∀ κ, J' (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r ≫ φ κ) = j₀) → val t (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r) z' J' = 1) → ∃ e₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) e₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ X) → L.ι), Good L z J → (∀ κ, J (r ≫ φ κ) = j₀) → val t r z J = gm (𝟙 _) z ⊤ (unitΓ e₀) := by
  intro X Y L hL B _ p K _ φ ε t r j₀ h₁ h₂
  have hW : (⊤ : (Sp (Jet B Unit p)).Opens) ≤ r ⁻¹ᵁ LB.wchart L φ (fun _ => j₀) :=
    fun q _ => Set.mem_iInter.2 fun κ => h₁ κ q
  obtain ⟨e₀, he₀⟩ := exists_unitΓ_eq (res hW (pullU r _ (t.s fun _ => j₀)))
  have key : ∀ (Z : Scheme.{0}) (f : Z ⟶ Sp (Jet B Unit p)) (z : Z),
      gm f z ⊤ (unitΓ e₀) = gm (f ≫ r) z (LB.wchart L φ (fun _ => j₀)) (t.s fun _ => j₀) := by
    intro Z f z
    rw [he₀, gm_res f z hW (Set.mem_univ _)]
    exact gm_pull f r z _ (hW (Set.mem_univ _)) _
  refine ⟨e₀, ?_, ?_⟩
  · have hv : pullU (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B)) ⊤ (unitΓ e₀) = 1 := by
      apply unit_ext
      intro z' _
      obtain ⟨J', hJ', e⟩ := exists_good L hL z'
        (fun κ => spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r ≫ φ κ) (fun _ => j₀)
        (fun _ _ _ => rfl) (fun κ => h₁ κ _)
      have hv := h₂ z' J' hJ' e
      rw [val_of t _ z' J' (fun _ => j₀) (fun κ => by rw [Category.assoc]; exact e κ), ← key] at hv
      have hp := gm_pull (𝟙 _) (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B)) z' ⊤ (Set.mem_univ _)
        (unitΓ e₀)
      rw [Category.id_comp] at hp
      rw [map_one]
      exact hp.trans hv
    apply toΓ_inj
    rw [map_one]
    exact (spMap_toΓ _ _).symm.trans (congrArg Units.val hv)
  · intro z J _ hc
    rw [val_of t r z J (fun _ => j₀) hc, key, Category.id_comp]

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

theorem le_wchart_one {X : Scheme.{0}} (L : LB X) (i : L.ι) :
    L.U i ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

def SameSec {X : Scheme.{0}} {L : LB X} (s : Out.H0 L 1) (th : L.Sec) : Prop :=
  ∀ i, th.f i = (X.presheaf.map (homOfLE (le_wchart_one L i)).op).hom (s.f fun _ => i)

def NonVan {S Y : Scheme.{0}} (p : Y ⟶ S) {M : LB Y} (s : M.Sec) : Prop :=
  ∀ b : S, ∃ y : Y, p y = b ∧ y ∈ Out.nonzeroLocus s

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleCocyclePullbackTransform
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem gm_appLE {X Y : Scheme.{0}} (a : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ a ⁻¹ᵁ U) (u : Γ(X, U)ˣ)
    {x : Y} (hx : x ∈ V) :
    gm (𝟙 Y) x V (Units.map (a.appLE U V h).hom.toMonoidHom u) = gm a x U u := by
  have e : Units.map (a.appLE U V h).hom.toMonoidHom u = res h (pullU a U u) := by
    apply Units.ext
    simp [res, pullU, Scheme.Hom.appLE]
  rw [e, gm_res _ x h hx, gm_pull (𝟙 Y) a x U (h hx) u, Category.id_comp]

theorem cob_group {G : Type} [CommGroup G] (p q r u v B T : G) (h₁ : p * q = v) (h₂ : r * u = v) :
    p * (q * B⁻¹ * T) = r * B⁻¹ * (u * T) := by
  calc p * (q * B⁻¹ * T) = p * q * (B⁻¹ * T) := by simp only [_root_.mul_assoc]
    _ = r * u * (B⁻¹ * T) := by rw [h₁, h₂]
    _ = r * B⁻¹ * (u * T) := mul_mul_mul_comm r u B⁻¹ T

theorem exists_gen_of_units (X Y : Scheme.{0}) (L : LB X) (hL : L.IsLB) (a b : Y ⟶ X) (hab : ∀ y, a y = b y)
    (t : ∀ j, Γ(Y, b ⁻¹ᵁ L.U j)ˣ)
    (ht : ∀ (j j' : L.ι) (h : b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ a ⁻¹ᵁ (L.U j ⊓ L.U j')),
      res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j from fun _ hy => hy.1) (t j) =
        Units.map (a.appLE _ _ h).hom.toMonoidHom (L.g j j') * (pullU b _ (L.g j j'))⁻¹ *
          res (show b ⁻¹ᵁ (L.U j ⊓ L.U j') ≤ b ⁻¹ᵁ L.U j' from fun _ hy => hy.2) (t j')) :
    ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![a, b] ![1, -1]), c.IsGen := by
  have hA : ∀ i : Fin 2 → L.ι, ∀ y ∈ LB.wchart L ![a, b] i, a y ∈ L.U (i 0) := fun i y hy =>
    Set.mem_iInter.1 hy 0
  have hB : ∀ i : Fin 2 → L.ι, ∀ y ∈ LB.wchart L ![a, b] i, b y ∈ L.U (i 1) := fun i y hy =>
    Set.mem_iInter.1 hy 1
  have hle : ∀ i : Fin 2 → L.ι, LB.wchart L ![a, b] i ≤ a ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i 1)) := fun i y hy =>
    ⟨hA i y hy, by
      show a y ∈ L.U (i 1)
      rw [hab y]; exact hB i y hy⟩
  have hle' : ∀ i : Fin 2 → L.ι, LB.wchart L ![a, b] i ≤ b ⁻¹ᵁ L.U (i 1) := fun i y hy => hB i y hy
  let s : ∀ i : Fin 2 → L.ι, Γ(Y, LB.wchart L ![a, b] i)ˣ := fun i =>
    res (hle i) (pullU a _ (L.g (i 0) (i 1))) * res (hle' i) (t (i 1))
  have hs : ∀ (i : Fin 2 → L.ι) (x : Y), x ∈ LB.wchart L ![a, b] i →
      gm (𝟙 Y) x _ (s i) = gm a x _ (L.g (i 0) (i 1)) * gm (𝟙 Y) x _ (t (i 1)) := by
    intro i x hx
    have h₁ : gm (𝟙 Y) x _ (res (hle i) (pullU a _ (L.g (i 0) (i 1)))) = gm a x _ (L.g (i 0) (i 1)) := by
      rw [gm_res _ x _ hx, gm_pull (𝟙 Y) a x _ (hle i hx), Category.id_comp]
    rw [map_mul, h₁, gm_res _ x _ hx]
  refine ⟨⟨s⟩, fun i i' => unit_ext fun x hx => ?_⟩
  have hmem : b x ∈ L.U (i 1) ⊓ L.U (i' 1) := ⟨hB i x hx.1, hB i' x hx.2⟩
  have hh : b ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)) ≤ a ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)) := fun y hy => by
    show a y ∈ L.U (i 1) ⊓ L.U (i' 1)
    rw [hab y]; exact hy
  have e := congrArg (gm (𝟙 Y) x (b ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)))) (ht (i 1) (i' 1) hh)
  have hmem' : x ∈ b ⁻¹ᵁ (L.U (i 1) ⊓ L.U (i' 1)) := hmem
  rw [map_mul, map_mul, map_inv, gm_res (𝟙 Y) x _ hmem', gm_res (𝟙 Y) x _ hmem', gm_appLE a hh _ hmem',
    gm_pull (𝟙 Y) b x _ hmem, Category.id_comp] at e
  have c₁ := gm_cocycle hL a x (hA i x hx.1) (show a x ∈ L.U (i 1) from (hle i hx.1).2)
    (show a x ∈ L.U (i' 1) from (hle i' hx.2).2)
  have c₂ := gm_cocycle hL a x (hA i x hx.1) (hA i' x hx.2) (show a x ∈ L.U (i' 1) from (hle i' hx.2).2)
  have hg := gm_linComb L ![a, b] ![1, -1] (𝟙 Y) x i i' hx.1 hx.2
  rw [gm_res _ x _ hx, map_mul, gm_res _ x _ hx]
  show gm (𝟙 Y) x (LB.wchart L ![a, b] i) (s i) =
    gm (𝟙 Y) x (LB.wchart L ![a, b] i ⊓ LB.wchart L ![a, b] i') ((LB.LinComb L ![a, b] ![1, -1]).g i i') *
      gm (𝟙 Y) x (LB.wchart L ![a, b] i') (s i')
  rw [hg, hs i x hx.1, hs i' x hx.2, e, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp, zpow_one, zpow_neg]
  exact cob_group _ _ _ _ _ _ _ c₁ c₂

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleSectionDifferenceGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

section TauGen

variable {X Y Z : Scheme.{0}} (L : LB X)

def gUnit (h : Y ⟶ X) (a b : L.ι) {V : Y.Opens} (hV : V ≤ h ⁻¹ᵁ (L.U a ⊓ L.U b)) : Γ(Y, V)ˣ :=
  res hV (pullU h _ (L.g a b))

theorem gm_gUnit (h : Y ⟶ X) (a b : L.ι) {V : Y.Opens} (hV : V ≤ h ⁻¹ᵁ (L.U a ⊓ L.U b)) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ V) : gm r z V (gUnit L h a b hV) = gm (r ≫ h) z _ (L.g a b) :=
  (gm_res r z hV hz _).trans (gm_pull r h z _ (hV hz) _)

def chartGen (f f' : Y ⟶ X) (b : L.ι) (hb : ∀ y, f y ∈ L.U b) (hb' : ∀ y, f' y ∈ L.U b) :
    LB.Gen (LB.LinComb L (K := Fin 2) ![f, f'] ![1, -1]) where
  s := fun i =>
    gUnit L f (i 0) b (V := LB.wchart L ![f, f'] i) (fun y hy => ⟨LB.wchart_le L ![f, f'] i 0 hy, hb y⟩) *
    (gUnit L f' (i 1) b (V := LB.wchart L ![f, f'] i) (fun y hy => ⟨LB.wchart_le L ![f, f'] i 1 hy, hb' y⟩))⁻¹

theorem gm_chartGen (f f' : Y ⟶ X) (b : L.ι) (hb : ∀ y, f y ∈ L.U b) (hb' : ∀ y, f' y ∈ L.U b)
    (i : Fin 2 → L.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ LB.wchart L ![f, f'] i) :
    gm r z (LB.wchart L ![f, f'] i) ((chartGen L f f' b hb hb').s i) =
      gm (r ≫ f) z _ (L.g (i 0) b) * (gm (r ≫ f') z _ (L.g (i 1) b))⁻¹ :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_gUnit L f _ _ _ r z hz)
    ((map_inv _ _).trans (congrArg _ (gm_gUnit L f' _ _ _ r z hz))))

theorem chartGen_isGen (hL : L.IsLB) (f f' : Y ⟶ X) (b : L.ι) (hb : ∀ y, f y ∈ L.U b) (hb' : ∀ y, f' y ∈ L.U b) :
    (chartGen L f f' b hb hb').IsGen := by
  intro (i : Fin 2 → L.ι) (j : Fin 2 → L.ι)
  refine unit_ext fun y hy => ?_
  have hi : (𝟙 Y) y ∈ LB.wchart L ![f, f'] i := hy.1
  have hj : (𝟙 Y) y ∈ LB.wchart L ![f, f'] j := hy.2
  have hi0 : (𝟙 Y ≫ f) y ∈ L.U (i 0) := LB.wchart_le L ![f, f'] i 0 hy.1
  have hi1 : (𝟙 Y ≫ f') y ∈ L.U (i 1) := LB.wchart_le L ![f, f'] i 1 hy.1
  have hj0 : (𝟙 Y ≫ f) y ∈ L.U (j 0) := LB.wchart_le L ![f, f'] j 0 hy.2
  have hj1 : (𝟙 Y ≫ f') y ∈ L.U (j 1) := LB.wchart_le L ![f, f'] j 1 hy.2
  have hb0 : (𝟙 Y ≫ f) y ∈ L.U b := hb y
  have hb1 : (𝟙 Y ≫ f') y ∈ L.U b := hb' y
  have A := gm_chartGen L f f' b hb hb' i (𝟙 Y) y hi
  have B := gm_chartGen L f f' b hb hb' j (𝟙 Y) y hj
  have C := gm_linComb L ![f, f'] ![1, -1] (𝟙 Y) y i j hi hj
  refine ((gm_res _ y _ hy _).trans A).trans (Eq.symm ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) C ((gm_res _ y _ hy _).trans B)).trans ?_)))
  have T : (∏ k, gm (𝟙 Y ≫ (![f, f'] : Fin 2 → (Y ⟶ X)) k) y (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)) ^
      (![1, -1] : Fin 2 → ℤ) k) = gm (𝟙 Y ≫ f) y _ (L.g (i 0) (j 0)) * (gm (𝟙 Y ≫ f') y _ (L.g (i 1) (j 1)))⁻¹ :=
    (Fin.prod_univ_two _).trans (congrArg₂ (· * ·) (zpow_one _) (zpow_neg_one _))
  rw [T, ← gm_cocycle hL (𝟙 Y ≫ f) y hi0 hj0 hb0, ← gm_cocycle hL (𝟙 Y ≫ f') y hi1 hj1 hb1, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

end TauGen

theorem jetPair_gen : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (k : Type) [Field k] (p : ℕ) (f f' : Sp (Jet k Unit p) ⟶ X), spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f = spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f' → ∃ τ : LB.Gen (LB.LinComb L (K := Fin 2) ![f, f'] ![1, -1]), τ.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ X) → L.ι), Good L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1 := by
  intro X L hL k _ p f f' e
  obtain ⟨s₀⟩ : Nonempty (Sp k) := inferInstance
  set w₀ : Sp (Jet k Unit p) := (spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) s₀ with hw
  have hq : ∀ q : Sp (Jet k Unit p), q = w₀ := fun q => (jet_pt p q s₀).symm
  have e₀ : f' w₀ = f w₀ := by
    have := congrArg (fun m => m s₀) e
    simpa using this.symm
  obtain ⟨b, hb₀⟩ := exists_chart hL (f w₀)
  have hb : ∀ y, f y ∈ L.U b := fun y => by rw [hq y]; exact hb₀
  have hb' : ∀ y, f' y ∈ L.U b := fun y => by rw [hq y, e₀]; exact hb₀
  refine ⟨chartGen L f f' b hb hb', chartGen_isGen L hL f f' b hb hb', ?_⟩
  intro Z' r z J hJ
  set ρ := r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) with hρ
  have eρ : ρ ≫ f = ρ ≫ f' := by rw [hρ, Category.assoc, Category.assoc, e]
  have hz := hJ.mem ![f, f'] ρ
  rw [val]
  refine (gm_chartGen L f f' b hb hb' _ ρ z hz).trans ?_
  have key : ∀ ψ ψ' : Z' ⟶ X, ψ = ψ' → gm ψ z (L.U (J ψ) ⊓ L.U b) (L.g (J ψ) b) =
      gm ψ' z (L.U (J ψ') ⊓ L.U b) (L.g (J ψ') b) := by
    rintro _ _ rfl
    rfl
  exact mul_inv_eq_one.2 (key _ _ eρ)

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TruncatedExpansionPthPowerCoeff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.CoefAlg

theorem pow_frobenius_truncated {B : Type} [CommRing B] (δ : B) (p : ℕ) [Fact p.Prime]
    (hp0 : (p : B) = 0) (hδ : δ ^ (p + 1) = 0) (a : Fin (p + 1) → B) (ha0 : a 0 = 1)
    (h1 : 1 < p + 1) :
    (∑ i, a i * δ ^ (i : ℕ)) ^ p = 1 + a ⟨1, h1⟩ ^ p * δ ^ p := by
  have hpp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hpp.two_le
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact Subsingleton.elim _ _
  haveI : CharP B p := by
    have h := CharP.ringChar_of_prime_eq_zero hpp hp0
    rw [← h]
    exact ringChar.charP B
  rw [sum_pow_char p]
  have hterm : ∀ i : Fin (p + 1), (a i * δ ^ (i : ℕ)) ^ p =
      (if i = 0 then 1 else 0) + (if i = ⟨1, h1⟩ then a ⟨1, h1⟩ ^ p * δ ^ p else 0) := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      have : (0 : Fin (p + 1)) ≠ ⟨1, h1⟩ := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [ha0, this]
    by_cases hi1 : i = ⟨1, h1⟩
    · subst hi1
      have : (⟨1, h1⟩ : Fin (p + 1)) ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [this, mul_pow]
    · have hv0 : (i : ℕ) ≠ 0 := fun h => hi0 (Fin.ext h)
      have hv1 : (i : ℕ) ≠ 1 := fun h => hi1 (Fin.ext h)
      have hv : 2 ≤ (i : ℕ) := by omega
      have hle : p + 1 ≤ (i : ℕ) * p := by nlinarith
      have hz : δ ^ ((i : ℕ) * p) = 0 := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
        rw [hk, pow_add, hδ, zero_mul]
      simp [hi0, hi1, mul_pow, ← pow_mul, hz]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem delta_pow_mul_truncated {B : Type} [CommRing B] (δ : B) (p : ℕ)
    (hδ : δ ^ (p + 1) = 0) (b : Fin (p + 1) → B) (hb0 : b 0 = 1) :
    δ ^ p * ∑ i, b i * δ ^ (i : ℕ) = δ ^ p := by
  rw [Fin.sum_univ_succ, mul_add, Finset.mul_sum]
  have hz : ∀ i : Fin p, δ ^ p * (b i.succ * δ ^ ((i.succ : Fin (p + 1)) : ℕ)) = 0 := by
    intro i
    have : δ ^ p * (b i.succ * δ ^ ((i.succ : Fin (p + 1)) : ℕ)) =
        b i.succ * (δ ^ (p + 1) * δ ^ (i : ℕ)) := by
      simp only [Fin.val_succ]
      ring
    rw [this, hδ]
    simp
  rw [Finset.sum_eq_zero (fun i _ => hz i)]
  simp [hb0]

theorem coeff_comparison : ∀ (A B : Type) [CommRing A] [CommRing B] (π : A →+* B) (δ : B) (p : ℕ) [Fact p.Prime], (p : B) = 0 → δ ^ (p + 1) = 0 → (∀ c c' : Fin (p + 1) → A, ∑ i, π (c i) * δ ^ (i : ℕ) = ∑ i, π (c' i) * δ ^ (i : ℕ) → c = c') → ∀ (u c₁ c₂ : Fin (p + 1) → A), u 0 = 1 → c₁ 0 = 1 → c₂ 0 = 1 → ∑ i, π (c₁ i) * δ ^ (i : ℕ) = (∑ i, π (u i) * δ ^ (i : ℕ)) ^ p * ∑ i, π (c₂ i) * δ ^ (i : ℕ) → c₁ (Fin.last p) = c₂ (Fin.last p) + u ⟨1, Nat.succ_lt_succ (Nat.Prime.pos Fact.out)⟩ ^ p := by
  intro A B _ _ π δ p _ hp0 hδ huniq u c₁ c₂ hu0 hc₁ hc₂ hmain
  have h1 : 1 < p + 1 := Nat.succ_lt_succ (Nat.Prime.pos Fact.out)
  have hfrob := pow_frobenius_truncated δ p hp0 hδ (fun i => π (u i)) (by simp [hu0]) h1
  have hdel := delta_pow_mul_truncated δ p hδ (fun i => π (c₂ i)) (by simp [hc₂])
  have hlast : ∀ i : Fin (p + 1),
      π (Function.update c₂ (Fin.last p) (c₂ (Fin.last p) + u ⟨1, h1⟩ ^ p) i) * δ ^ (i : ℕ) =
        π (c₂ i) * δ ^ (i : ℕ) +
          (if i = Fin.last p then π (u ⟨1, h1⟩) ^ p * δ ^ p else 0) := by
    intro i
    by_cases hi : i = Fin.last p
    · subst hi
      simp [add_mul]
    · simp [Function.update_of_ne hi, hi]
  have hsum : ∑ i, π (c₁ i) * δ ^ (i : ℕ) = ∑ i,
      π (Function.update c₂ (Fin.last p) (c₂ (Fin.last p) + u ⟨1, h1⟩ ^ p) i) * δ ^ (i : ℕ) := by
    simp only [hlast, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hmain, hfrob, add_mul, _root_.one_mul, _root_.mul_assoc, hdel]
  have := huniq _ _ hsum
  rw [this]
  simp

end GlobalTheory.CompanionTheory.Ar.CoefAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistModelsCommonPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TwoModels

theorem generic_fibre_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (π' : Z ⟶ Y'.X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (x x' : Sp Ω ⟶ Xo.XF c), ξ ≫ π = x ≫ Y.j → ξ ≫ π' = x' ≫ Y'.j → x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → ∃ (t t' : SAB H Z) (tΩ : SAB H (Sp Ω)) (a : SABMap t Y.t π) (a' : SABMap t' Y'.t π') (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ) (u : SABMap tΩ Y.oF.t x) (u' : SABMap (twistSAB tΩ g) Y'.oF.t x'), m.φ ≫ a.φ = u.φ ≫ Y.m.φ ∧ m'.φ ≫ a'.φ = u'.φ ≫ Y'.m.φ ∧ u'.φ ≫ Y'.m0.toSABMap.φ = (twistMap u g).φ ≫ (twistMap Y.m0.toSABMap g).φ ≫ n.φ :=
  @PositivityTheory.UnitarySelfGeneration.two_models_common_cover_compare

end GlobalTheory.CompanionTheory.Ar.TwoModels
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZeroSectionSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem tensor_isPullback {X0 : Scheme.{0}} (A B : Over X0) :
    IsPullback (fst A B).left (snd A B).left A.hom B.hom :=
  IsPullback.of_hasPullback A.hom B.hom

theorem secZ_isPullback {X0 : Scheme.{0}} (G : Over X0) {k : Type} [Field k] (x : Sp k ⟶ X0) (m : ℕ) :
    IsPullback (secZ G x m) (pullback.snd G.hom x) (fst (Tm x m) G).left
      (spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) := by
  have hR := (tensor_isPullback (Tm x m) G).flip
  have hO : IsPullback (secZ G x m ≫ (snd (Tm x m) G).left) (pullback.snd G.hom x) G.hom
      (spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k) ≫ (Tm x m).hom) := by
    rw [secZ_snd]
    have e : spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k) ≫ (Tm x m).hom = x := by
      dsimp
      rw [← Category.assoc, spMap_comp_alg]
      simp [spMap]
    rw [e]
    exact IsPullback.of_hasPullback G.hom x
  exact IsPullback.of_right hO (secZ_fst G x m) hR

theorem secZ_surj (X0 : Scheme.{0}) (G : Over X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (m : ℕ) :
    Function.Surjective (secZ G x m).base := by
  have hs : Surjective (spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) := ⟨fun q =>
    ⟨IsLocalRing.closedPoint k, jet_pt m q _⟩⟩
  have := MorphismProperty.of_isPullback (P := @Surjective) (secZ_isPullback G x m).flip hs
  exact this.surj

end GlobalTheory.CompanionTheory.Ar.Coc
end

