module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0170
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegEigLatEqOfIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF


open IntCoord in
theorem diff_mem_eigLat {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} {f : P.A ⟶ P'.A}
    (hf : ∀ x, a.act x ≫ f = f ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    (hM : F.IsDiffOf F' f M) (τ : O →+* 𝓞 K) {c : Fin F.P₀.g → K} (hc : c ∈ F.eigLat a τ) :
    M c ∈ F'.eigLat a' τ := by
  obtain ⟨u, hu, he⟩ := ((integral_tangent_coordinates K P F).2.2.2.2.2 O a τ c).1 hc
  refine Submodule.subset_span ⟨u ≫ f, hM u c hu, fun x => ?_⟩
  rw [isLieComb_one_iff, Category.assoc, ← hf, ← Category.assoc, (isLieComb_one_iff _ _ _).1 (he x),
    Category.assoc]

theorem map_eigLat_of_iso {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} {F : GenFib P}
    {F' : GenFib P'} {O : Type} [CommRing O] {a : OAct O P.A} {a' : OAct O P'.A} (e : P.A ≅ P'.A)
    (hf : ∀ x, a.act x ≫ e.hom = e.hom ≫ a'.act x) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    {M' : (Fin F'.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)}
    (hM : F.IsDiffOf F' e.hom M) (hM' : F'.IsDiffOf F e.inv M') (τ : O →+* 𝓞 K) :
    (F.eigLat a τ).map (M.restrictScalars (𝓞 K)) = F'.eigLat a' τ := by
  refine le_antisymm ?_ fun c hc => ?_
  · rintro _ ⟨c, hc, rfl⟩
    exact diff_mem_eigLat hf hM τ hc
  · have hf' : ∀ x, a'.act x ≫ e.inv = e.inv ≫ a.act x := fun x => by
      rw [Iso.comp_inv_eq, Category.assoc, hf, Iso.inv_hom_id_assoc]
    refine ⟨M' c, diff_mem_eigLat hf' hM' τ hc, ?_⟩
    obtain ⟨u, hu, -⟩ := ((integral_tangent_coordinates K P' F').2.2.2.2.2 O a' τ c).1 hc
    have h2 := hM _ _ (hM' _ _ hu)
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h2
    exact ((integral_tangent_coordinates K P' F').1 u hu.1).unique h2 hu

theorem deg_eigLat_eq_of_iso : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P P' : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (O : Type) [CommRing O] (a : OAct O P.A) (a' : OAct O P'.A) (e : P.A ≅ P'.A), F.IsHerm h → F'.IsHerm h' → Serre.IsLinearHom a a' e.hom → LamEq P'.L e.hom e.hom P.L (𝟙 P.A) (𝟙 P.A) → ∀ τ : O →+* 𝓞 K, deg h (F.eigLat a τ) = deg h' (F'.eigLat a' τ) := by
  intro hT hL K _ _ P P' F F' h h' O _ a a' e hh hh' hlin hlam τ
  have hm : IsMonHom e.hom := hlin.1
  have hm' : IsMonHom e.inv := inferInstance
  obtain ⟨M, hM, -⟩ := (_root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P' F' e.hom hm).1
  obtain ⟨M', hM', -⟩ := (_root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P' F' P F e.inv hm').1
  have hid : F.IsDiffOf F (𝟙 P.A) LinearMap.id := fun u c hu => by simpa using hu
  have hiso := _root_.GlobalTheory.HermHom.form_diff_eq hT hL K P F P' F' h h' e.hom (𝟙 P.A) M LinearMap.id hh hh' hm inferInstance hlam hM hid
  have hle : F.eigLat a τ ≤ F.lieLat := Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩
  have hfg : (F.eigLat a τ).FG := (_root_.GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K P F).1.of_le hle
  rw [← map_eigLat_of_iso e hlin.2 hM hM' τ]
  exact (deg_map_isometry K _ _ h h' M _ hfg hiso).symm

end GlobalTheory.LamF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegreeLieLatticeHermitianInvariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FibIndep

section Lattice

variable {K : Type*} [Field K] [NumberField K] {V V' : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']


open scoped ComplexOrder in
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] in
theorem injective_of_isometry (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V')
    (hM : ∀ s c c', h'.form s (M c) (M c') = h.form s c c') : Function.Injective M := by
  obtain ⟨s⟩ : Nonempty (K →+* ℂ) := inferInstance
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  by_contra hne
  have hli : LinearIndependent K ![c] := (linearIndependent_unique_iff (v := ![c])).2 (by simpa using hne)
  have hpos := (h.posDef s 1 ![c] hli).diag_pos (i := 0)
  have hzero : h'.form s 0 0 = 0 := by simpa using h'.smul_right s 0 0 0
  have hcc : h.form s c c = 0 := by rw [← hM, hc, hzero]
  simp only [Matrix.of_apply, Matrix.cons_val_fin_one] at hpos
  rw [hcc] at hpos
  exact lt_irrefl _ hpos

theorem deg_map_of_isometry (h : HermFam K V) (h' : HermFam K V') (M : V →ₗ[K] V')
    (hM : ∀ s c c', h'.form s (M c) (M c') = h.form s c c') {E : Submodule (𝓞 K) V} (hE : E.FG) :
    deg h E = deg h' (E.map (M.restrictScalars (𝓞 K))) := by
  have hinj := injective_of_isometry h h' M hM
  obtain ⟨v, hv⟩ := exists_isFrame E hE
  obtain ⟨hvE, hvli, hvsp⟩ := hv
  have hv' : IsFrame K (E.map (M.restrictScalars (𝓞 K))) (M ∘ v) := by
    refine ⟨fun i => Submodule.mem_map_of_mem (hvE i), hvli.map' M (LinearMap.ker_eq_bot.2 hinj), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hvsp hx
    rw [Set.range_comp, Submodule.span_image]
    exact Submodule.mem_map_of_mem hx'
  rw [arakelovDegree_eq_degreeOfFamily h hE ⟨hvE, hvli, hvsp⟩, arakelovDegree_eq_degreeOfFamily h' (hE.map _) hv']
  have hgram : ∀ σ, h'.gram σ (M ∘ v) = h.gram σ v := fun σ => by
    ext i j
    simp [HermFam.gram, hM]
  have hspan : Submodule.span (𝓞 K) (Set.range (M ∘ v)) =
      (Submodule.span (𝓞 K) (Set.range v)).map (M.restrictScalars (𝓞 K)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hidx : (Submodule.span (𝓞 K) (Set.range (M ∘ v))).toAddSubgroup.relIndex
      (E.map (M.restrictScalars (𝓞 K))).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup := by
    rw [hspan, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  unfold degreeOfFamily
  rw [hidx]
  simp only [hgram]

end Lattice

variable {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp (𝓞 K))}

theorem existsUnique_coord (F : GenFib P) {u : epsR (𝓞 K) ⟶ P.A} (hu : IsTangent u) : ∃! c, F.IsCoord u c := by
  have hb := F.basis
  unfold IsLieBasis at hb
  have hf := F.fib
  unfold IsPolFibre at hf
  obtain ⟨-, hpb, -⟩ := hf
  obtain ⟨w, hw, hwu⟩ := existsUnique_isVecOver hpb.1 u
  obtain ⟨c, hc, hcu⟩ := hb.2 w (hw.isTangent hpb hu)
  refine ⟨c, ⟨hu, w, hw, hc⟩, ?_⟩
  rintro c' ⟨-, w', hw', hc'⟩
  obtain rfl := hwu w' hw'
  exact hcu c' hc'

theorem image_coord (F F' : GenFib P) {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)} (hM : F.IsDiffOf F' (𝟙 P.A) M)
    (p : (epsR (𝓞 K) ⟶ P.A) → Prop) :
    Submodule.span (𝓞 K) {c | ∃ u, F'.IsCoord u c ∧ p u} =
      (Submodule.span (𝓞 K) {c | ∃ u, F.IsCoord u c ∧ p u}).map (M.restrictScalars (𝓞 K)) := by
  rw [Submodule.map_span]
  congr 1
  ext c
  constructor
  · rintro ⟨u, hu, hp⟩
    obtain ⟨ht, -⟩ := id hu
    obtain ⟨c₀, hc₀, -⟩ := existsUnique_coord F ht
    refine ⟨c₀, ⟨u, hc₀, hp⟩, ?_⟩
    have h1 := hM u c₀ hc₀
    rw [Category.comp_id] at h1
    exact (existsUnique_coord F' ht).unique h1 hu
  · rintro ⟨c₀, ⟨u, hu, hp⟩, rfl⟩
    have h1 := hM u c₀ hu
    rw [Category.comp_id] at h1
    exact ⟨u, h1, hp⟩

theorem deg_lieLat_eq : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P) (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → deg h F.lieLat = deg h' F'.lieLat ∧ ∀ (O : Type) [CommRing O] (act : OAct O P.A) (τ : O →+* 𝓞 K), deg h (F.eigLat act τ) = deg h' (F'.eigLat act τ) := by
  intro hU hL K _ _ P F F' h h' hh hh'
  obtain ⟨⟨M, hM, -⟩, -⟩ := _root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P F' (𝟙 P.A) inferInstance
  have hN : F.IsDiffOf F (𝟙 P.A) LinearMap.id := fun u c hc => by
    rw [Category.comp_id]
    exact hc
  have hlam : LamEq P.L (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) :=
    GlobalTheory.PolBaseChange.lbIso_refl (GlobalTheory.LamCalc.cubeLB_isLB P.isLB _)
  have hiso : ∀ s c c', h'.form s (M c) (M c') = h.form s c c' := fun s c c' => by
    simpa using _root_.GlobalTheory.HermHom.form_diff_eq hU hL K P F P F' h h' (𝟙 P.A) (𝟙 P.A) M LinearMap.id hh hh'
      inferInstance inferInstance hlam hM hN s c c'
  have hFG := (_root_.GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K P F).1
  refine ⟨?_, fun O _ act τ => ?_⟩
  · have e := image_coord F F' hM (fun _ => True)
    simp only [and_true] at e
    have e' : F'.lieLat = F.lieLat.map (M.restrictScalars (𝓞 K)) := e
    rw [e']
    exact deg_map_of_isometry h h' M hiso hFG
  · have e := image_coord F F' hM (fun u => ∀ a, IsLieComb ![τ a] ![u] (u ≫ act.act a))
    have hle : F.eigLat act τ ≤ F.lieLat :=
      Submodule.span_mono fun c ⟨u, hu, _⟩ => ⟨u, hu⟩
    have hFG' : (F.eigLat act τ).FG := hFG.of_le hle
    have e' : F'.eigLat act τ = (F.eigLat act τ).map (M.restrictScalars (𝓞 K)) := e
    rw [e']
    exact deg_map_of_isometry h h' M hiso hFG'

end GlobalTheory.FibIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianLengthImageEigenBasisVectorLe
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.LenOne

theorem re_form_smul_le {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (h : HermFam K V)
    (s : K →+* ℂ) (t : K) {x : V} (hx : x ≠ 0) : (h.form s x (t • x)).re ≤ ‖s t‖ * (h.form s x x).re := by
  have hp := (h.posDef s 1 ![x] (by simpa [linearIndependent_unique_iff] using hx)).diag_pos (i := 0)
  have hp' : 0 < h.form s x x := by simpa using hp
  obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hp'
  rw [h.smul_right, Complex.mul_re, ← h2, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_right (Complex.re_le_norm _) h1.le

theorem diff_single_eq {K : Type} [Field K] [NumberField K] {P P' : Out.PolAV (Sp (𝓞 K))} (F : GenFib P)
    (F' : GenFib P') {f : P.A ⟶ P'.A} {f₀ : F.P₀.A ⟶ F'.P₀.A} (e : f₀.left ≫ F'.φ = F.φ ≫ f.left)
    {M : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K)}
    (hM : ∀ c w, IsLieComb c F.v w → IsLieComb (M c) F'.v (w ≫ f₀)) (i : Fin F.P₀.g) {U : Fin F'.P₀.g → K}
    {w : epsR K ⟶ F'.P₀.A} (hU : IsLieComb U F'.v w) (hw : w.left ≫ F'.φ = (F.v i).left ≫ F.φ ≫ f.left) :
    M (Pi.single i 1) = U := by
  have := F.P₀.isAb.comm
  have := F'.P₀.isAb.comm
  obtain rfl : w = F.v i ≫ f₀ := Over.OverMorphism.ext (F'.fib.2.1.1.hom_ext
    (by rw [hw, Over.comp_left, Category.assoc, e]) ((Over.w _).trans (Over.w _).symm))
  exact (F'.basis.2 _ ((LieComb.lieComb_algebra K _ _ F'.v F'.basis.1).2.1 U _ hU)).unique
    (hM _ _ ((LieComb.lieComb_algebra K _ _ F.v F.basis.1).2.2.2.1 i)) hU

theorem form_image_le : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P P' : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A), F.IsHerm h → F'.IsHerm h' → IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → ∀ (i : Fin F.P₀.g) (t : K) (w : epsR K ⟶ F.P₀.A) (U : Fin F'.P₀.g → K) (w' : epsR K ⟶ F'.P₀.A), IsLieComb (Pi.single i t) F.v w → (F.v i).left ≫ F.φ ≫ g.left = w.left ≫ F.φ → IsLieComb U F'.v w' → w'.left ≫ F'.φ = (F.v i).left ≫ F.φ ≫ f.left → ∀ s : K →+* ℂ, (h'.form s U U).re ≤ ‖s t‖ * (h.form s (Pi.single i 1) (Pi.single i 1)).re := by
  intro hT hL K _ _ P P' F F' h h' f g hh hh' hf hg hlam i t w U w' hw ew hU ew' s
  obtain ⟨⟨M, hM, -⟩, f₀, -, ef, hf₀⟩ := _root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P' F' f hf
  obtain ⟨⟨N, hN, -⟩, g₀, -, eg, hg₀⟩ := _root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K P F P F g hg
  have h1 := diff_single_eq F F' ef (hf₀ M hM) i hU ew'
  have h2 := diff_single_eq F F eg (hg₀ N hN) i hw ew.symm
  have h3 := _root_.GlobalTheory.HermHom.form_diff_eq hT hL K P F P' F' h h' f g M N hh hh' hf hg hlam hM hN s (Pi.single i 1) (Pi.single i 1)
  have h4 : (Pi.single i t : Fin F.P₀.g → K) = t • (Pi.single i 1 : Fin F.P₀.g → K) := by
    rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [h1, h2, h4] at h3
  rw [h3]
  exact re_form_smul_le h s t (by simp)

end GlobalTheory.LamF.LenOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LambdaBundleIsoOfWeilPairingCompatible
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.LamOfWeil

open ReciprocityTheory.ChartRestriction.G.Out CommutatorPairing DescentPairing IsoDescent

section

variable {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] [IsCommMonObj A]

abbrev sqφ (a b : T ⟶ A) : ULift.{0} (Finset (Fin 2)) → (T.left ⟶ A.left) := fun I => (psum A ![a, b] I.down).left

abbrev sqε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem prod_sq (ρ : T' ⟶ T) (a b : T ⟶ A) {U : Type} [CommGroup U] (h : (T'.left ⟶ A.left) → U) :
    ∏ I, h (ρ.left ≫ sqφ a b I) ^ sqε I =
      h ((ρ ≫ a) * (ρ ≫ b)).left * (h (ρ ≫ a).left)⁻¹ * (h (ρ ≫ b).left)⁻¹ * h (1 : T' ⟶ A).left := by
  have p := NormRos.prod_square a b (fun q => h (ρ.left ≫ q))
  simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one] at p
  exact p

theorem exists_gen_axis {L : LB A.left} (hL : L.IsLB) (ρ : T' ⟶ T) (a b : T ⟶ A) (H : ρ ≫ a = 1 ∨ ρ ≫ b = 1) :
    ∃ t : LB.Gen (LB.LinComb L (fun I => ρ.left ≫ sqφ a b I) sqε), t.IsGen :=
  AdjointOfPairing.exists_gen_of_formEq_zero hL fun U _ h => by
    rw [prod_sq]
    rcases H with H | H
    · rw [H, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    · rw [H, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel

end

theorem exists_gen_div {X X' Y Y' : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] (L : LB X) (L' : LB X')
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X')) (ε' : K' → ℤ) (f : Y' ⟶ Y)
    (H : LBIso (LB.LinComb L (fun k => f ≫ φ k) ε) (LB.LinComb L' (fun k => f ≫ φ' k) ε')) :
    ∃ t : LB.Gen ((LB.div (LB.LinComb L' φ' ε') (LB.LinComb L φ ε)).pull f), t.IsGen := by
  obtain ⟨w, hw⟩ := H.chartPull (chartPullOut L φ ε f _ fun _ => rfl) (chartPullOut L' φ' ε' f _ fun _ => rfl)
  exact gen_chartPull (IsoDescent.chartPullDiv _ _ f) w hw

variable {k : Type} [Field k] {X Y : Over (Sp k)} [GrpObj X] [GrpObj Y]

theorem exists_gen_fibre (hG : GlobalFnsSt) (hC : CubeSt) (P : PolAV (Sp k)) (f₁ : X ⟶ P.A) (f₂ : Y ⟶ P.A)
    [IsMonHom f₁] [IsMonHom f₂] (n : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ X) (hx : x ^ n = 1) :
    ∃ u : LB.Gen (LB.LinComb P.L (fun I => (mulA Y n).left ≫ (lift (toUnit Y ≫ x) (𝟙 Y)).left ≫
        sqφ (fst X Y ≫ f₁) (snd X Y ≫ f₂) I) sqε),
      u.IsGen ∧ ∀ (y : 𝟙_ (Over (Sp k)) ⟶ Y) (c : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), y ^ n = 1 →
        WeilIs P.A P.L n (x ≫ f₁) (y ≫ f₂) c → ∀ (z : Y.left) (J), Good P.L z J →
          val u ((toUnit Y ≫ y) * 𝟙 Y).left z J = val u (𝟙 _) z J * gm (toUnit Y).left z ⊤ c := by
  have := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨⟨cb⟩, -⟩ := hC _ P L rfl
  let T := 𝟙_ (Over (Sp k))
  let p₀ : T.left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : T.left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have hx₁ : (x ≫ f₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  obtain ⟨u₀, hu₀, v₀⟩ := PairingDetermines.exists_gen_transl hG P.isAb cb p₀ hT n (x ≫ f₁) hx₁
  obtain ⟨σ, hσ⟩ := exists_frame P.isLB (K := Fin 2) ![(x ≫ f₁).left, (1 : T ⟶ P.A).left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, v⟩ := exists_gen P.isLB
    (φ' := fun I => (mulA Y n).left ≫ (lift (toUnit Y ≫ x) (𝟙 Y)).left ≫
      sqφ (fst X Y ≫ f₁) (snd X Y ≫ f₂) I) (ε' := sqε)
    (fun U _ h => by
      have e₀ : mulA Y n ≫ lift (toUnit Y ≫ x) (𝟙 Y) = lift (toUnit Y ≫ x) (𝟙 Y ^ n) := by
        rw [comp_lift, comp_toUnit_assoc, Category.comp_id]
      have e₁ : lift (toUnit Y) f₂ ≫ mulT P.A T n ≫ translPt P.A (x ≫ f₁) =
          (toUnit Y ≫ x ≫ f₁) * ((𝟙 Y ^ n) ≫ f₂) := by
        rw [← Category.assoc, mulT, comp_lift, lift_translPt, lift_fst, MonObj.comp_pow, lift_snd,
          MonObj.pow_comp, Category.id_comp]
      have e₂ : lift (toUnit Y) f₂ ≫ snd T P.A ^ n = (𝟙 Y ^ n) ≫ f₂ := by
        rw [MonObj.comp_pow, lift_snd, MonObj.pow_comp, Category.id_comp]
      have e₃ : toUnit Y ≫ (1 : T ⟶ P.A) = 1 := MonObj.comp_one _
      have e := prod_sq (lift (toUnit Y ≫ x) (𝟙 Y ^ n)) (fst X Y ≫ f₁) (snd X Y ≫ f₂) h
      rw [lift_fst_assoc, lift_snd_assoc, Category.assoc] at e
      refine Eq.trans ?_ (e.symm.trans (Finset.prod_congr rfl fun I _ => by
        rw [← e₀, Over.comp_left, Category.assoc]))
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, ← Over.comp_left, e₁, e₂, e₃, Category.assoc, zpow_neg, zpow_one, _root_.mul_one]
      ac_rfl)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ u₀ (lift (toUnit Y) f₂).left) (LB.pullGen P.L _ _ σ (toUnit Y).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨u, hu, fun y c hy hc z J hJ => ?_⟩
  have hy₂ : (y ≫ f₂) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have w : ∀ a : Y ⟶ Y, val u a.left z J =
      val u₀ (lift (toUnit Y) (a ≫ f₂)).left z J * val σ (toUnit Y).left z J := fun a => by
    rw [v _ _ z J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      comp_toUnit]
  have w₀ := v₀ (y ≫ f₂) c hy₂ hc Y (toUnit Y) (𝟙 Y ≫ f₂) z J hJ
  refine (w _).trans (Eq.trans ?_ (congrArg (· * _) (w (𝟙 Y))).symm)
  rw [MonObj.mul_comp, Category.assoc, mul_right_comm]
  exact congrArg (fun q => q * _) w₀

end GlobalTheory.CM.LamOfWeil

namespace GlobalTheory.CM

open LamOfWeil IsoDescent

theorem lamEq_of_weilEq : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X Y A B : Out.PolAV (Sp k)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp k)) → LamEq A.L f₁ f₂ B.L g₁ g₂ := by
  intro hL k _ _ _ X Y A B f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ hW
  haveI : IsCommMonObj A.A := A.isAb.comm
  haveI : IsCommMonObj B.A := B.isAb.comm
  haveI : IsCommMonObj Y.A := Y.isAb.comm
  have axis : ∀ {Z : Over (Sp k)} (ρ : Z ⟶ X.A ⊗ Y.A), ρ ≫ fst _ _ = 1 ∨ ρ ≫ snd _ _ = 1 →
      ∃ t : LB.Gen ((LB.div (LB.LinComb B.L (sqφ (fst X.A Y.A ≫ g₁) (snd X.A Y.A ≫ g₂)) sqε)
        (LB.LinComb A.L (sqφ (fst X.A Y.A ≫ f₁) (snd X.A Y.A ≫ f₂)) sqε)).pull ρ.left), t.IsGen := by
    intro Z ρ H
    obtain ⟨u, hu⟩ := exists_gen_axis A.isLB ρ (fst X.A Y.A ≫ f₁) (snd X.A Y.A ≫ f₂)
      (H.imp (fun h => by rw [reassoc_of% h, MonObj.one_comp]) (fun h => by rw [reassoc_of% h, MonObj.one_comp]))
    obtain ⟨u', hu'⟩ := exists_gen_axis B.isLB ρ (fst X.A Y.A ≫ g₁) (snd X.A Y.A ≫ g₂)
      (H.imp (fun h => by rw [reassoc_of% h, MonObj.one_comp]) (fun h => by rw [reassoc_of% h, MonObj.one_comp]))
    exact exists_gen_div _ _ _ _ _ _ _ (lbIso_of_gens A.isLB B.isLB _ _ _ _ u hu u' hu')
  refine _root_.GlobalTheory.triv_of_triv_on_dense_fibres_prod_abelian hL.globalFns k X.A Y.A
    (LB.div (LB.LinComb B.L (sqφ (fst X.A Y.A ≫ g₁) (snd X.A Y.A ≫ g₂)) sqε)
      (LB.LinComb A.L (sqφ (fst X.A Y.A ≫ f₁) (snd X.A Y.A ≫ f₂)) sqε)) Y.L X.isAb Y.isAb Y.isLB Y.ample
    (LB.isLB_div (DVR.linComb_isLB _ B.isLB _ _) (DVR.linComb_isLB _ A.isLB _ _))
    (axis _ (Or.inl (lift_fst _ _))) ?_ (axis _ (Or.inr (lift_snd _ _)))
  refine (TorsionDense.dense_torsion X hL.irred hL.kerPow).mono (Set.biUnion_subset_biUnion_left ?_)
  rintro x ⟨n, hn, hx⟩
  obtain ⟨u, hu, v⟩ := exists_gen_fibre hL.globalFns hL.cube A f₁ f₂ n x hx
  obtain ⟨u', hu', v'⟩ := exists_gen_fibre hL.globalFns hL.cube B g₁ g₂ n x hx
  refine exists_gen_div _ _ _ _ _ _ _ ?_
  refine lbIso_of_invariant A.isLB B.isLB _ _ _ _ (Out.mulA Y.A n).left
    (I := {y : 𝟙_ (Over (Sp k)) ⟶ Y.A // y ^ n = 1}) (fun y => ((toUnit Y.A ≫ y.1) * 𝟙 Y.A).left) (fun y => ?_)
    (fun U f hf => torsion_invariant_descends (fun S _ P n hn => by
      obtain ⟨a, b, c, e, -⟩ := hL.mulN S P n hn
      exact ⟨a, b, c, e⟩) k Y n (Nat.cast_ne_zero.2 hn.ne') U f fun y hy => hf ⟨y, hy⟩) u hu u' hu'
    (fun y z J J' hJ hJ' => ?_)
  · rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, y.2,
      MonObj.comp_one, _root_.one_mul]
  · have hx₁ : (x ≫ f₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    have hy₂ : (y.1 ≫ f₂) ^ n = 1 := by rw [← MonObj.pow_comp, y.2, MonObj.one_comp]
    obtain ⟨c, hc, -⟩ := (hL.weil _ A n _).1 (x ≫ f₁) (y.1 ≫ f₂) hx₁ hy₂
    obtain ⟨c, rfl⟩ : ∃ c₀ : kˣ, unitOn c₀ = c :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom c,
        Units.ext ((Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply c.val)⟩
    have h₁ := v y.1 (unitOn c) y.2 hc z J hJ
    have h₂ := v' y.1 (unitOn c) y.2 ((hW n x y.1 c hn hx y.2).1 hc) z J' hJ'
    refine (congrArg₂ (fun a b => a * b⁻¹) h₂ h₁).trans ?_
    exact mul_div_mul_right_eq_div _ _ _ |> fun h => by simpa only [div_eq_mul_inv] using h

end GlobalTheory.CM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingHomExtRingOfIntegers
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.EigLine

theorem ringHom_ext_ringOfIntegers {E K : Type} [Field E] [NumberField E] [Field K] {f g : E →+* K}
    (h : ∀ a : 𝓞 E, f (a : E) = g (a : E)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem forall_apply_eq_smul_iff {K O : Type} [Field K] {n : ℕ} (r : O → Module.End K (Fin n → K)) (χ : Fin n → O → K)
    (hχ : Function.Injective χ) (hr : ∀ a j, r a (Pi.single j 1) = Pi.single j (χ j a)) (i : Fin n) (c : Fin n → K) :
    (∀ a, r a c = χ i a • c) ↔ ∃ s : K, c = Pi.single i s := by
  have hd : ∀ a (d : Fin n → K) j, r a d j = χ j a * d j := fun a d j => by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [pi_eq_sum_univ' d, map_sum]
    simp only [map_smul, hr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk.symm]) (by simp), Pi.single_eq_same,
      mul_comm]
  constructor
  · intro h
    refine ⟨c i, funext fun j => ?_⟩
    by_cases hj : j = i
    · rw [hj, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hj]
      by_contra hc
      refine hj (hχ (funext fun a => mul_right_cancel₀ hc ?_))
      rw [← hd, h a, Pi.smul_apply, smul_eq_mul]
  · rintro ⟨s, rfl⟩ a
    funext j
    rw [hd, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = i
    · rw [hj]
    · rw [Pi.single_eq_of_ne hj, mul_zero, mul_zero]

theorem mem_eigLat_iff : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (oa : A.OAct (𝓞 E)) (act : OAct (𝓞 E) A.A) (S : Set (E →+* ℂ)) (τ : Fin x.P.g ≃ S) (lab : (E →+* ℂ) → (E →+* K)), act.act = oa.act → Function.Injective lab → IsLieType A oa x φ τ lab → ∀ (i : Fin x.P.g) (t : 𝓞 E →+* 𝓞 K), (∀ a : 𝓞 E, (t a : K) = lab (τ i) (a : E)) → ∀ c, c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).eigLat act t ↔ c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat ∧ ∃ r : K, c = Pi.single i r := by
  intro E _ _ _ K _ _ A x φ hf oa act S τ lab hact hlab hty i t ht c
  obtain ⟨r, hr, he⟩ := _root_.GlobalTheory.CM.GenFib.exists_lieRep_eigLat K A (GenFib.mk x.P φ hf x.v x.basis) (𝓞 E) act
  have := x.P.isAb.comm
  have halg := LieComb.lieComb_algebra K x.P.A x.P.g x.v x.basis.1
  have hdiag : ∀ (a : 𝓞 E) (j : Fin x.P.g), r a (Pi.single j 1) = Pi.single j (lab (τ j) (a : E)) := fun a j => by
    obtain ⟨-, f₀, -, e, h⟩ := _root_.GlobalTheory.CM.DiffCoord.existsUnique_isDiffOf K A (GenFib.mk x.P φ hf x.v x.basis) A (GenFib.mk x.P φ hf x.v x.basis)
      (act.act a) (act.hom a)
    obtain ⟨w, hw, hw'⟩ := hty a j
    have h₁ : IsLieComb (r a (Pi.single j 1)) x.v (x.v j ≫ f₀) := h _ (hr a) _ _ (halg.2.2.2.1 j)
    have e' : f₀.left ≫ φ = φ ≫ (oa.act a).left := by rw [← hact]; exact e
    obtain rfl : x.v j ≫ f₀ = w := Over.OverMorphism.ext (hf.2.1.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, e', hw']) ((Over.w _).trans (Over.w _).symm))
    exact (x.basis.2 _ (halg.2.1 _ _ hw)).unique h₁ hw
  have hχ : Function.Injective fun (j : Fin x.P.g) (a : 𝓞 E) => lab (τ j) (a : E) := fun j k h =>
    τ.injective (Subtype.ext (hlab (ringHom_ext_ringOfIntegers fun a => congrFun h a)))
  refine (he t c).1.trans (and_congr_right fun _ => ?_)
  rw [← forall_apply_eq_smul_iff (fun a => r a) _ hχ hdiag i c]
  refine forall_congr' fun a => ?_
  rw [← ht a, ← algebraMap_smul K (t a) c]

end GlobalTheory.LamF.EigLine
end

