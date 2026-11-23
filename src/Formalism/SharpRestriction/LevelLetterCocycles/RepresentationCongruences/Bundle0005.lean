module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0012
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftLeEPA
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AevalDopMap
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Polynomial

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable (W : LocWach PD LL O v n)

private theorem π₀_cancel (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T : LocLat G Qp LL O}
    {a b : W.DD T} (h : W.π₀ • a = W.π₀ • b) : a = b := by
  obtain ⟨u, hu⟩ := hπ
  have ha : W.π₀ • a = (u : W.EE) • a := by rw [hu, algebraMap_smul]
  have hb : W.π₀ • b = (u : W.EE) • b := by rw [hu, algebraMap_smul]
  calc a = (↑u⁻¹ : W.EE) • ((u : W.EE) • a) := by rw [smul_smul, Units.inv_mul, one_smul]
    _ = (↑u⁻¹ : W.EE) • ((u : W.EE) • b) := by rw [← ha, h, hb]
    _ = b := by rw [smul_smul, Units.inv_mul, one_smul]

theorem dop_eq (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (T : LocLat G Qp LL O)
    (dop : W.DD T →ₗ[O] W.DD T) (hd : ∀ y, W.π₀ • dop y = W.γ T y - y) {x y : W.DD T}
    (h : W.γ T x - x = W.π₀ • y) : dop x = y :=
  π₀_cancel W hπ ((hd x).trans h)

theorem dop_pres (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (T : LocLat G Qp LL O) (i : ZMod n)
    (dop : W.DD T →ₗ[O] W.DD T) (hd : ∀ y, W.π₀ • dop y = W.γ T y - y)
    (hgN : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T i y ∧ W.γ T x - x = W.π₀ • y)
    {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (dop x) := by
  obtain ⟨y, hy, hxy⟩ := hgN x hx
  rw [dop_eq W hπ T dop hd hxy]
  exact hy

theorem dop_map (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L)
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y) (y : W.DD T₁) :
    W.map F (dop₁ y) = dop₂ (W.map F y) := by
  apply π₀_cancel W hπ
  have hs : ∀ z : W.DD T₁, W.π₀ • W.map F z = W.map F (W.π₀ • z) := fun z => by
    rw [← algebraMap_smul W.EE W.π₀ (W.map F z), ← map_smul, algebraMap_smul]
  rw [hs, hd₁, hd₂, map_sub]
  congr 1
  exact W.map_γ F W.gam y

theorem aeval_dop_map (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L)
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y) (p : O[X]) (y : W.DD T₁) :
    W.map F (aeval dop₁ p y) = aeval dop₂ p (W.map F y) := by
  have hO : ∀ (c : O) (v : W.DD T₁), W.map F (c • v) = c • W.map F v := by
    intro c v
    rw [← algebraMap_smul (LetA O n) c v, ← algebraMap_smul W.EE (algebraMap O (LetA O n) c) v, map_smul,
      algebraMap_smul, algebraMap_smul]
  have hc : ∀ k : ℕ, ∀ y : W.DD T₁, W.map F ((dop₁ ^ k) y) = (dop₂ ^ k) (W.map F y) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, dop_map W hπ F dop₁ hd₁ dop₂ hd₂, ih]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.sum_apply,
    map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hO, hc]

theorem dop_inImg (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (i : ZMod n)
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (hgN₁ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i y ∧ W.γ T₁ x - x = W.π₀ • y)
    {z : W.DD T₂} (hz : InImg W F i z) : InImg W F i (dop₂ z) := by
  unfold InImg at hz ⊢
  obtain ⟨x₁, hx₁, rfl⟩ := hz
  exact ⟨dop₁ x₁, dop_pres W hπ T₁ i dop₁ hd₁ hgN₁ hx₁, dop_map W hπ F dop₁ hd₁ dop₂ hd₂ x₁⟩

private theorem nΔi_add' {T : LocLat G Qp LL O} {i : ZMod n} {x y : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) (hy : Formalism.MainNotions.LiftingTheory.InNΔi W T i y) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T i (x + y) := by
  unfold Formalism.MainNotions.LiftingTheory.InNΔi at *
  exact ⟨(W.NΔ T).add_mem hx.1 hy.1, (W.Nl T i).add_mem hx.2 hy.2⟩

private theorem nΔi_smulO' {T : LocLat G Qp LL O} {i : ZMod n} (c : O) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (c • x) := by
  unfold Formalism.MainNotions.LiftingTheory.InNΔi at *
  refine ⟨(W.NΔ T).smul_mem c hx.1, ?_⟩
  rw [← algebraMap_smul (LetA O n) c x]
  exact (W.Nl T i).smul_mem _ hx.2

private theorem nΔi_aeval (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (T : LocLat G Qp LL O)
    (i : ZMod n) (dop : W.DD T →ₗ[O] W.DD T) (hd : ∀ y, W.π₀ • dop y = W.γ T y - y)
    (hgN : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T i y ∧ W.γ T x - x = W.π₀ • y)
    (p : O[X]) {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T i (aeval dop p x) := by
  have hpow : ∀ k : ℕ, ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T i x → Formalism.MainNotions.LiftingTheory.InNΔi W T i ((dop ^ k) x) := by
    intro k
    induction k with
    | zero => intro x hx; rw [pow_zero, Module.End.one_apply]; exact hx
    | succ k ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      exact dop_pres W hπ T i dop hd hgN (ih x hx)
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  refine Finset.sum_induction _ (Formalism.MainNotions.LiftingTheory.InNΔi W T i) (fun a b ha hb => nΔi_add' W ha hb) ?_ ?_
  · unfold Formalism.MainNotions.LiftingTheory.InNΔi
    exact ⟨(W.NΔ T).zero_mem, (W.Nl T i).zero_mem⟩
  · intro k _
    rw [LinearMap.smul_apply]
    exact nΔi_smulO' W _ (hpow k x hx)

theorem aeval_inImg (hπ : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (i : ZMod n)
    (dop₁ : W.DD T₁ →ₗ[O] W.DD T₁) (hd₁ : ∀ y, W.π₀ • dop₁ y = W.γ T₁ y - y)
    (dop₂ : W.DD T₂ →ₗ[O] W.DD T₂) (hd₂ : ∀ y, W.π₀ • dop₂ y = W.γ T₂ y - y)
    (hgN₁ : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i x → ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i y ∧ W.γ T₁ x - x = W.π₀ • y)
    (p : O[X]) {z : W.DD T₂} (hz : InImg W F i z) : InImg W F i (aeval dop₂ p z) := by
  unfold InImg at hz ⊢
  obtain ⟨x₁, hx₁, rfl⟩ := hz
  exact ⟨aeval dop₁ p x₁, nΔi_aeval W hπ T₁ i dop₁ hd₁ hgN₁ p hx₁,
    aeval_dop_map W hπ F dop₁ hd₁ dop₂ hd₂ p x₁⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CocycleClassesExponent
section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {PD : PeriodData G Qp K₀ K B BdR}

theorem cocycle_classes_exponent {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (e : ℕ)
    (Zc : Finset (LatticeCohomology T₂.L))
    (hZc : ∀ z ∈ Zc, z ∈ latticeFiniteCohomology PD T₂.L)
    (h : ∀ x ∈ latticeFiniteCohomology PD T₂.L, (((PD.p : ℕ) : O) ^ e) • x ∈
      (latticeFiniteCohomology PD T₁.L).map F.H1map ⊔ Submodule.span O (Zc : Set (LatticeCohomology T₂.L))) :
    ∃ Z : Finset (G → T₂.V), Z.card ≤ Zc.card ∧ (∀ z ∈ Z, z ∈ latticeFiniteCocycles PD T₂.L) ∧ ExpIn PD F Z e := by
  classical
  have hrep : ∀ z ∈ Zc, ∃ a : ↥(latticeCocycles T₂.L), (a : G → T₂.V) ∈ latticeFiniteCocycles PD T₂.L ∧ Submodule.mkQ _ a = z := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp (hZc z hz)
    exact ⟨a, ha, rfl⟩
  choose! r hr1 hr2 using hrep
  refine ⟨Zc.image (fun z => (r z : G → T₂.V)), Finset.card_image_le, ?_, ?_⟩
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact hr1 z hz
  · intro c hc
    have hc' : c ∈ latticeCocycles T₂.L ⊓ _ := hc
    have hcZ : c ∈ latticeCocycles T₂.L := (Submodule.mem_inf.mp hc').1
    have hx : Submodule.mkQ _ (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) ∈ latticeFiniteCohomology PD T₂.L :=
      Submodule.mem_map_of_mem (p := (latticeFiniteCocycles PD T₂.L).comap (latticeCocycles T₂.L).subtype) hc
    obtain ⟨y, hy, w, hw, hyw⟩ := Submodule.mem_sup.mp (h _ hx)
    obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hy0
    have ha' : (a : G → T₁.V) ∈ latticeFiniteCocycles PD T₁.L := ha
    have hspan : Submodule.span O (Zc : Set (LatticeCohomology T₂.L)) =
        (Submodule.span O (r '' (Zc : Set (LatticeCohomology T₂.L)))).map (Submodule.mkQ _) := by
      rw [Submodule.map_span, Set.image_image, Set.image_congr (g := fun z => z) (fun z hz => hr2 z hz),
        Set.image_id']
    rw [hspan] at hw
    obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hw
    have e1 : F.H1map (Submodule.mkQ _ a) =
        Submodule.mkQ _ (⟨F.post a, F.post_Z1T _ a.2⟩ : ↥(latticeCocycles T₂.L)) := rfl
    have hker : ((PD.p : ℕ) : O) ^ e • (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) -
        ⟨F.post a, F.post_Z1T _ a.2⟩ - s ∈ (latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype := by
      rw [← Submodule.ker_mkQ ((latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype), LinearMap.mem_ker, map_sub, map_sub,
        map_smul, ← hyw, e1]
      abel
    have hb : ((PD.p : ℕ) : O) ^ e • c - F.post a - (s : G → T₂.V) ∈ latticeCoboundaries T₂.L := hker
    have hs' : (s : G → T₂.V) ∈
        Submodule.span O ((Zc.image fun z => (r z : G → T₂.V) : Finset (G → T₂.V)) : Set (G → T₂.V)) := by
      have hm := Submodule.mem_map_of_mem (f := (latticeCocycles T₂.L).subtype) hs
      rw [Submodule.map_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hz)
    have hpa : F.post a ∈ F.ImF PD := Submodule.mem_sup_left (Submodule.mem_map_of_mem ha')
    have hbI : ((PD.p : ℕ) : O) ^ e • c - F.post a - (s : G → T₂.V) ∈ F.ImF PD := Submodule.mem_sup_right hb
    have key : ((PD.p : ℕ) : O) ^ e • c =
        (F.post a + (((PD.p : ℕ) : O) ^ e • c - F.post a - (s : G → T₂.V))) + s := by abel
    rw [key]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.add_mem _ hpa hbI)) (Submodule.mem_sup_right hs')

end Core

end Formalism.MainNotions.N.Ln17
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsLiftFLeSgOfThick
section
namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
theorem exists_liftF_le_sg_of_thick : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) {CR CA CB CK : ℝ} (hU : AdmBoundsB D HW F Cm CR CA CB CK)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)]
    (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : LatHom T₁.L T₂.L) (b w S η m : ℕ)
    (up : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool) (size Mi hi : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ)
    (hB : HypB ((D.loc l).PD K) ((HW l).W K 1 LL hG) T₁ T₂ f b w S η m up size Mi hi)
    (hAlt : Alt b η up size) (hth : ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i)
    (hbig : (b : ℝ) / 4 < 40 * Sg l b w S η size),
    ∃ e₀ : ℕ, (e₀ : ℝ) ≤ 160 * Sg l b w S η size ∧ f.LiftF ((D.loc l).PD K) e₀ := by
  intro D HW F Cm CR CA CB CK hU l _ K LL hG hK _ _ T₁ T₂ f b w S η m up size Mi hi hB hAlt hth hbig
  obtain ⟨hp11, hSet, hwb, hηb, hSb, ⟨j, hj⟩⟩ := hB
  obtain ⟨hCA, hSur, hηs, hJA, _hlow, hnt, _hJL⟩ := hSet
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hl : 11 ≤ l := hp ▸ hp11
  have hLift : Formalism.MainNotions.LiftingTheory.coreLiftA ((HW l).W K 1 LL hG) := hU.a2.2.2.2.2.2.2.2.1 l K 1 LL hG

  have hsz : ∀ i, size i ≤ b + η := by
    intro i
    by_cases ht : TruncatedSeriesCountingBounds.Thick b η size i
    · exact ht.2
    · have := hnt i ht
      omega
  have hb1 : 1 ≤ b := by
    have h1 := hnt j hj
    have h2 := hηs j
    omega
  have hhB : TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := if_pos hth

  let Mi' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ := fun i => if up i then η else size i + S
  let hi' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ := fun i => if up i then size i + S else η
  have hJL' : Formalism.MainNotions.LiftingTheory.JumpsLet ((HW l).W K 1 LL hG) T₁ Mi' hi' := by
    intro i τ hτ a ha
    have h1 := hJA i τ hτ a ha
    have h2 := hηs i
    cases hu : up i
    · simp only [hu, Mi', hi', Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
    · simp only [hu, Mi', hi', if_true, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hM : Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi' ≤ b + η + S := by
    apply Finset.sup_le
    intro k _
    have h1 := hsz (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    cases hu : up (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) <;>
      simp only [hu, Mi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hm : Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) hi' ≤ b + η + S := by
    apply Finset.sup_le
    intro k _
    have h1 := hsz (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    cases hu : up (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) <;>
      simp only [hu, hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hH : Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi' hi' ≤ b + η + S + η := by
    apply Finset.sup_le
    intro k _
    have h1 := hsz (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    cases hu : up (k : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) <;>
      simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hjumps : ∀ u ∈ Formalism.MainNotions.LiftingTheory.jumpSet ((HW l).W K 1 LL hG) T₁
      (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi')
      (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) hi'),
      -((Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi' : ℕ) : ℤ) ≤ u ∧
        u ≤ ((b + η + S : ℕ) : ℤ) := by
    intro u hu
    simp only [Formalism.MainNotions.LiftingTheory.jumpSet, Finset.mem_filter, Finset.mem_Icc] at hu
    refine ⟨hu.1.1, ?_⟩
    have := hu.1.2
    push_cast at this ⊢
    omega
  have hL := Formalism.MainNotions.N.FrobeniusPowerSeries.lift_le_ePA l hl (b + η + S) η
    (Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi' hi')
    (Formalism.MainNotions.LiftingTheory.Mmax (Module.finrank ℚ_[l] ↥(K0 K)) Mi') (by omega) (by omega) hH hM _ hjumps
  have hSg : Sg l b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg l (b + η + S) w S η := by
    unfold Sg Formalism.MainNotions.N.FrobeniusPowerSeries.Sg
    rw [hhB]
  have h0 := Formalism.MainNotions.N.FrobeniusPowerSeries.step0 l hl b w S η hb1 hηb hSb hwb (by rw [← hSg]; exact hbig)
  have hLA := hLift hCA T₁ T₂ f Mi' hi' hSur hJL'
  refine ⟨_, ?_, hLA⟩
  rw [hp, hSg]
  linarith

end Formalism.MainNotions.N.Ln17
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.HmaxLe
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem hmax_le' [NeZero n] (Mi hi : ZMod n → ℕ) (j : ZMod n) :
    Mi j + hi j ≤ Formalism.MainNotions.LiftingTheory.Hmax n Mi hi := by
  unfold Formalism.MainNotions.LiftingTheory.Hmax
  have h := Finset.le_sup (f := fun k : ℕ => Mi k + hi k) (Finset.mem_range.2 (ZMod.val_lt j))
  simp only [ZMod.natCast_zmod_val] at h
  exact h

theorem aI_le [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR) (c : ZMod n)
    (hct : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c) (hc1 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c + 1)) :
    (Formalism.MainNotions.LiftingTheory.AI W F (c - 1) : ℝ) ≤
      ((size c : ℝ) + S + η) / PD.p + 2 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
  obtain ⟨hp11, hSet, hwb, hηb, hSb, -⟩ := hB
  obtain ⟨hcase, hSur, hηs, hJA, -, hnt, -⟩ := hSet
  let Mi' : ZMod n → ℕ := fun i => if up i then η else size i + S
  let hi' : ZMod n → ℕ := fun i => if up i then size i + S else η
  have hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi' hi' := by
    intro i τ hτ a ha
    have h1 := hJA i τ hτ a ha
    have h2 := hηs i
    cases hu : up i
    · simp only [hu, Mi', hi', Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
    · simp only [hu, Mi', hi', if_true, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hwid : ∀ i, Mi' i + hi' i = size i + S + η := by
    intro i
    cases hu : up i <;> simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hsz : ∀ i, size i ≤ b + η := by
    intro i
    by_cases ht : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i
    · exact ht.2
    · have := hnt i ht; omega
  have hHle : Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' ≤ (b + η + S) + η :=
    Finset.sup_le fun k _ => by rw [hwid]; have := hsz (k : ZMod n); omega
  obtain ⟨hs, -⟩ := hWR hcase T₁ T₂ F Mi' hi' hSur hJ (c - 1)
  have hcW : (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) =
      (cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) := rfl
  have e0 : c - 1 + ((0 + 1 : ℕ) : ZMod n) = c := by push_cast; ring
  have e1 : c - 1 + ((1 + 1 : ℕ) : ZMod n) = c + 1 := by push_cast; ring
  have hc1w : size (c + 1) ≤ w := hnt (c + 1) hc1
  have ht := tsum_three PD.p hp11
    (fun a => ((Mi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) + hi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) +
      Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    ((((size c + S + η : ℕ) : ℝ)) + cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    ((((w + S + η : ℕ) : ℝ)) + cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    ((Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' : ℝ) + cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    (fun a => by positivity)
    (by
      show _ + _ + _ ≤ _
      rw [e0, hwid, hcW])
    (by
      show _ + _ + _ ≤ _
      rw [e1, hwid, hcW]
      have : ((size (c + 1) + S + η : ℕ) : ℝ) ≤ ((w + S + η : ℕ) : ℝ) := by
        exact_mod_cast (by omega : size (c + 1) + S + η ≤ w + S + η)
      linarith)
    (fun a _ => by
      have := hmax_le' Mi' hi' (c - 1 + ((a + 1 : ℕ) : ZMod n))
      have h' : (((Mi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) + hi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ)) ≤
          Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' := by exact_mod_cast this
      show _ + _ + _ ≤ _
      rw [hcW]; linarith)
  have hst := hs.trans ht
  have hx : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp11
  have hA : (Formalism.MainNotions.LiftingTheory.AI W F (c - 1) : ℝ) ≤ (Formalism.MainNotions.LiftingTheory.sI W F (c - 1) : ℝ) / ((PD.p : ℝ) - 1) + 1 := by
    unfold Formalism.MainNotions.LiftingTheory.AI
    have h0 : 0 ≤ (Formalism.MainNotions.LiftingTheory.sI W F (c - 1) : ℝ) / ((PD.p : ℝ) - 1) :=
      div_nonneg (Nat.cast_nonneg _) (by linarith)
    exact (Nat.ceil_lt_add_one h0).le
  have hη1 : η + 1 ≤ b + η + S := by have := hηs c; have := hct.2; omega
  have key := Aa_cut_le PD.p hp11 (b + η + S) w S η (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') (size c + S + η)
    (w + S + η) hη1 hHle (by have := hct.2; omega) le_rfl _ _ hst hA
  have ec : (((size c + S + η : ℕ) : ℝ)) = (size c : ℝ) + S + η := by push_cast; ring
  rw [ec] at key
  exact key

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsLE
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthOneTwo

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem lifts_lE (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)
    {f : W.EE} {k e : ℕ} (h : LiftsAt W A F c b sol k₀ (lE W k * f) e) :
    LiftsAt W A F c b sol k₀ f (k + e) := by
  unfold LiftsAt at h ⊢
  obtain ⟨w₁, z, h1, h2, h3, h4, h5⟩ := h
  refine ⟨w₁, z, h1, h2, h3, h4, ?_⟩
  have hl : lE W e * (lE W k * f) = lE W (k + e) * f := by
    unfold lE
    ring
  rw [hl] at h5
  exact h5

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthOneTwo
end
end

