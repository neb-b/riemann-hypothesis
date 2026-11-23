module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultipleOfHermitianFormSumOfNorms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.HermSq

section general

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (br : R →+* R)

def IsSumOfNorms (B : M → M → R) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (l : J → M →ₗ[R] R), ∀ x y, B x y = ∑ k, l k x * br (l k y)

variable {br}

theorem IsSumOfNorms.congr {B B' : M → M → R} (h : IsSumOfNorms br B) (e : ∀ x y, B' x y = B x y) : IsSumOfNorms br B' := by
  obtain ⟨J, _, l, hl⟩ := h
  exact ⟨J, inferInstance, l, fun x y => (e x y).trans (hl x y)⟩

theorem IsSumOfNorms.zero : IsSumOfNorms br (fun (_ _ : M) => (0 : R)) :=
  ⟨Empty, inferInstance, fun e => e.elim, fun x y => by simp⟩

theorem IsSumOfNorms.one (f : M →ₗ[R] R) : IsSumOfNorms br (fun x y => f x * br (f y)) :=
  ⟨Unit, inferInstance, fun _ => f, fun x y => by simp⟩

theorem IsSumOfNorms.add {B B' : M → M → R} (h : IsSumOfNorms br B) (h' : IsSumOfNorms br B') :
    IsSumOfNorms br (fun x y => B x y + B' x y) := by
  obtain ⟨J, _, l, hl⟩ := h
  obtain ⟨J', _, l', hl'⟩ := h'
  refine ⟨J ⊕ J', inferInstance, Sum.elim l l', fun x y => ?_⟩
  simp [Fintype.sum_sum_type, hl, hl']

theorem IsSumOfNorms.nsmul {B : M → M → R} (h : IsSumOfNorms br B) (n : ℕ) :
    IsSumOfNorms br (fun x y => (n : R) * B x y) := by
  induction n with
  | zero => exact IsSumOfNorms.zero.congr fun x y => by simp
  | succ n ih => exact (ih.add h).congr fun x y => by push_cast; ring

theorem IsSumOfNorms.comp {B : M → M → R} (h : IsSumOfNorms br B) (Z : M →ₗ[R] M) :
    IsSumOfNorms br (fun x y => B (Z x) (Z y)) := by
  obtain ⟨J, _, l, hl⟩ := h
  exact ⟨J, inferInstance, fun k => l k ∘ₗ Z, fun x y => hl _ _⟩

theorem IsSumOfNorms.sum {κ : Type} (s : Finset κ) {B : κ → M → M → R} (h : ∀ i, IsSumOfNorms br (B i)) :
    IsSumOfNorms br (fun x y => ∑ i ∈ s, B i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact IsSumOfNorms.zero.congr fun x y => by simp
  | insert a s ha ih => exact ((h a).add ih).congr fun x y => by rw [Finset.sum_insert ha]

variable (g : M → M →ₗ[R] R) (herm : ∀ x y, g x y = br (g y x))


include herm in
theorem exists_step (e : M) (q : ℕ) (hq : g e e = q) :
    ∃ Z : M →ₗ[R] M, Z e = 0 ∧
      ∀ x y, g (Z y) (Z x) = (q : R) ^ 2 * g y x - q * (g e x * br (g e y)) := by
  refine ⟨(q : R) • LinearMap.id - (g e).smulRight e, by simp [hq], fun x y => ?_⟩
  have h1 : ∀ a, g (((q : R) • LinearMap.id - (g e).smulRight e : M →ₗ[R] M) y) a
      = q * g y a - br (g e y) * g e a := by
    intro a
    rw [herm]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      map_sub, map_smul, smul_eq_mul, map_mul, map_natCast]
    rw [← herm, ← herm e a]
  rw [h1]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      map_sub, map_smul, smul_eq_mul, hq]
  rw [herm y e]
  ring

variable (pos : ∀ x, x ≠ 0 → ∃ q : ℕ, 1 ≤ q ∧ g x x = q)

include herm pos in
theorem exists_kill {κ : Type} (v : κ → M) (s : Finset κ) :
    ∃ (N : ℕ) (Z : M →ₗ[R] M), 1 ≤ N ∧ (∀ i ∈ s, Z (v i) = 0) ∧
      IsSumOfNorms br (fun x y => (N : R) * g y x - g (Z y) (Z x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, LinearMap.id, le_rfl, by simp, IsSumOfNorms.zero.congr fun x y => by simp⟩
  | insert a s ha ih =>
    obtain ⟨N, Z, hN, hZ, hB⟩ := ih
    by_cases he : Z (v a) = 0
    · refine ⟨N, Z, hN, fun i hi => ?_, hB⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      exacts [he, hZ i hi]
    · obtain ⟨q, hq1, hq⟩ := pos _ he
      obtain ⟨Y, hY, hY'⟩ := exists_step g herm _ q hq
      refine ⟨q ^ 2 * N, Y ∘ₗ Z, Nat.mul_pos (pow_pos hq1 2) hN, fun i hi => ?_, ?_⟩
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · exact hY
        · simp [hZ i hi]
      · refine ((hB.nsmul (q ^ 2)).add (((IsSumOfNorms.one (g (Z (v a)))).comp Z).nsmul q)).congr fun x y => ?_
        simp only [LinearMap.comp_apply, hY']
        push_cast
        ring


include herm pos in
theorem exists_split {n : ℕ} (u w : Fin n → M) (fr : ∀ a, a = ∑ i, g (w i) a • u i) :
    ∃ (N m : ℕ) (l : M →ₗ[R] (Fin m → R)) (r : (Fin m → R) →ₗ[R] M), 1 ≤ N ∧ r ∘ₗ l = LinearMap.id ∧
      ∀ x y, (N : R) * g y x = ∑ k, l x k * br (l y k) := by
  classical
  obtain ⟨N, Z, hN, hZ, hB⟩ := exists_kill g herm pos u Finset.univ
  have hZ0 : ∀ a, Z a = 0 := fun a => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [fr a, map_sum]
    exact Finset.sum_eq_zero fun i hi => by rw [map_smul, hZ i hi, smul_zero]
  have hB' : IsSumOfNorms br (fun x y => (N : R) * g y x) := hB.congr fun x y => by simp [hZ0]
  have key : ∀ e : M, ∃ K : ℕ, IsSumOfNorms br (fun x y => (K : R) * g y x - g e x * br (g e y)) := by
    intro e
    by_cases he : e = 0
    · refine ⟨0, IsSumOfNorms.zero.congr fun x y => ?_⟩
      subst he
      rw [herm 0 x]; simp
    · obtain ⟨q, hq1, hq⟩ := pos _ he
      obtain ⟨Y, -, hY'⟩ := exists_step g herm _ q hq
      obtain ⟨c, hc⟩ : ∃ c : ℕ, N * q = c + 1 := ⟨N * q - 1, by have := Nat.mul_pos hN hq1; omega⟩
      have hc' : (N : R) * q = c + 1 := by exact_mod_cast congrArg (Nat.cast : ℕ → R) hc
      refine ⟨N * q ^ 2, ((hB'.comp Y).add ((IsSumOfNorms.one (g e)).nsmul c)).congr fun x y => ?_⟩
      simp only [hY']
      push_cast
      linear_combination (g e x * br (g e y)) * hc'
  choose K hK using key
  obtain ⟨J, _, l, hl⟩ := hB'.add (IsSumOfNorms.sum Finset.univ fun i => hK (w i))
  let eqv := Fintype.equivFin (Fin n ⊕ J)
  refine ⟨N + ∑ i, K (w i), Fintype.card (Fin n ⊕ J),
    LinearMap.pi fun k => Sum.elim (fun i => g (w i)) l (eqv.symm k),
    ∑ i, (LinearMap.proj (eqv (Sum.inl i)) : (Fin _ → R) →ₗ[R] R).smulRight (u i), by omega, ?_, fun x y => ?_⟩
  · ext a
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      LinearMap.pi_apply, Equiv.symm_apply_apply, Sum.elim_inl, LinearMap.id_apply]
    exact (fr a).symm
  · simp only [LinearMap.pi_apply]
    rw [eqv.symm.sum_comp (fun k => Sum.elim (fun i => g (w i)) l k x * br (Sum.elim (fun i => g (w i)) l k y)),
      Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← hl x y]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul]
    push_cast
    ring

end general

theorem kForm_sum_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ (N m : ℕ) (l : D.La →ₗ[OK H] (Fin m → OK H)) (r : (Fin m → OK H) →ₗ[OK H] D.La), 1 ≤ N ∧ r ∘ₗ l = LinearMap.id ∧ ∀ x y, (N : 𝓞 E) * (h x y : OK H) = ∑ k, ((l x k : OK H) : 𝓞 E) * H.bar (l y k : OK H) := by
  intro E _ _ _ H D ε h hh hpos
  obtain ⟨h₀, -, huniq, hherm, -, hdiag, -, n, u, w, fr⟩ := GlobalTheory.CM.exists_kForm E H D ε
  obtain ⟨-, -, ⟨br, hbr, -⟩, -⟩ := GlobalTheory.CM.OK_isDedekindDomain_and_projective E H
  obtain rfl := huniq h hh
  let g : D.La → D.La →ₗ[OK H] OK H := fun y =>
    { toFun := fun x => h₀ x y
      map_add' := fun a b => by rw [map_add (f := _)]; rfl
      map_smul' := fun c a => by rw [map_smul]; rfl }
  obtain ⟨N, m, l, r, hN, hr, hl⟩ := exists_split (br := br.toRingHom) g
    (fun x y => Subtype.ext ((hherm x y).trans (hbr _).symm))
    (fun x hx => by
      have h1 := hpos x hx
      refine ⟨((ε : ℤ) * D.EF (H.w0 • x) x).toNat, by omega, Subtype.ext ?_⟩
      refine (hdiag x).trans ?_
      conv_lhs => rw [← Int.toNat_of_nonneg h1.le]
      rw [Int.cast_natCast, SubringClass.coe_natCast]) u w fr
  refine ⟨N, m, l, r, hN, hr, fun x y => ?_⟩
  have := congrArg (OK H).val (hl x y)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_sum, map_natCast, Subalgebra.coe_val] at this
  simp only [← hbr]
  exact this

end GlobalTheory.CM.HermSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SabMapCancelAndCompOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory

theorem sabMap_cancel_and_comp_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S₁ S₂ : Scheme.{0}) (t : SAB H S) (t₁ : SAB H S₁) (t₂ : SAB H S₂) (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S) (g : S₂ ⟶ S₁) (m₁ : SABMap t₁ t f₁) (m₂ : SABMap t₂ t f₂), f₂ = g ≫ f₁ → (∃ n : SABMap t₂ t₁ g, n.φ ≫ m₁.φ = m₂.φ) ∧ ∀ n : SABMap t₂ t₁ g, ∃ m : SABMap t₂ t f₂, m.φ = n.φ ≫ m₁.φ := by
  intro E _ _ _ H S S₁ S₂ t t₁ t₂ f₁ f₂ g m₁ m₂ h
  subst h
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ t t₁ t₂ f₁ g m₁ m₂
  exact ⟨⟨n, hn.symm⟩, fun n => sabComp pullCubComp E H _ _ _ t t₁ t₂ f₁ g m₁ n⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SecTieBaseChange
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.TieCalc

theorem isoMaps_iff {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (σ : LB.Sec L') (s : LB.Sec (L.pull F)) :
    IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have a := congrArg (gs r z _) (h (fun _ => j) k)
    exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))
  · intro h (i : PUnit → L.ι) k
    exact fn_ext fun p hp =>
      (gs_res _ p _ hp _).trans ((h _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans
        (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t : SAB H (Sp S)} (m : SABMap t Xo.univ.t x)

theorem exists_canon : ∃ g : t.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ ∧
    g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t.G.hom := by
  let a₀ : Over.mk (t.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t.G.hom rfl
  let b₀ : Over.mk (t.G.hom ≫ x) ⟶ Xo.univ.t.G := Over.homMk m.φ m.cart.1.w
  exact ⟨(lift a₀ b₀).left, congrArg (fun q => q.left) (lift_snd a₀ b₀), congrArg (fun q => q.left) (lift_fst a₀ b₀)⟩

theorem canon_mem {g : t.G.left ⟶ Gx x} (hg : g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ)
    (j : Xo.univ.t.PP.L.ι) (y : t.G.left) (hy : m.φ y ∈ Xo.univ.t.PP.L.U j) : g y ∈ (PPx x).U (fun _ => j) :=
  Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) hg).mpr hy

theorem rigIso_unique {w w' : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m.φ)} (h : RigIso m w) (h' : RigIso m w') :
    w = w' := by
  have hp : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper
  have hab : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  exact GlobalTheory.iso_eq_of_maps_along_section (S := Sp S) (exists_chart t.PP.isLB)
    (fun y => (exists_chart Xo.univ.t.PP.isLB (m.φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    t.G.hom (eSec t.G) (Over.w η[t.G]) (GlobalTheory.globalFns_holds _ _ hab).2 h.1 h'.1 h.2 h'.2

theorem secTie_iff {w : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m.φ)} (hw : RigIso m w) {g : t.G.left ⟶ Gx x}
    (hs : g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ) (hf : g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t.G.hom)
    (th : LB.Sec t.PP.L) (s : LB.Sec (PPx x)) :
    SecTie m th s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (k : t.PP.L.ι),
      m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ t.PP.L.U k →
      gs (r ≫ g) z ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (th.f k) := by
  constructor
  · rintro ⟨w', s1, r1, i1, c⟩ Z r z j k hj hk
    obtain rfl : w' = w := rigIso_unique m r1 hw
    have le : (Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j) :=
      fun q hq => canon_mem m hs j q (mem_pull.1 hq)
    refine Eq.trans ?_ ((isoMaps_iff w' th s1).1 i1 Z r z j k hj hk)
    rw [c g hs hf (fun _ => j) le]
    exact (gs_appLE g _ _ le r z (mem_pull.2 hj) _).symm
  · intro a
    obtain ⟨s1, hs1⟩ := thf_secUp ((isGen_iff w).1 hw.1) Xo.univ.t.PP.isLB t.PP.isLB th
    refine ⟨w, s1, hw, (isoMaps_iff w th s1).2 fun Z r z j k hj hk => hs1 Z r z (fun _ => j) k (mem_pull.2 hj) hk, ?_⟩
    intro g' e₁ e₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
    obtain rfl : g' = g := SecCalc.pm_ext _ _ (e₁.trans hs.symm) (e₂.trans hf.symm)
    refine fn_ext fun p hp => ?_
    obtain ⟨k, hk⟩ := exists_chart t.PP.isLB p
    rw [hs1 _ (𝟙 _) p J k hp hk, gs_appLE _ _ _ hJ (𝟙 _) p hp, a _ (𝟙 _) p _ k (mem_pull.1 hp) hk]

theorem secTie_scale {th th' : LB.Sec t.PP.L} {s s' : LB.Sec (PPx x)} (h : SecTie m th s) (a : S)
    (hs' : ∀ i, s'.f i = scal x a i * s.f i) :
    SecTie m th' s' ↔ ∀ i, th'.f i = constFn t.G.hom _ a * th.f i := by
  obtain ⟨g, hs, hf⟩ := exists_canon m
  obtain ⟨w, -, hw, -⟩ := id h
  rw [secTie_iff m hw hs hf] at h ⊢
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (k : t.PP.L.ι),
      m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ t.PP.L.U k →
      gs (r ≫ g) z ((PPx x).U (fun _ => j)) (s'.f (fun _ => j)) =
        (gw w r z j k).val * gs r z _ (constFn t.G.hom _ a * th.f k) := by
    intro Z r z j k hj hk
    have a₁ : (r ≫ g) z ∈ (PPx x).U (fun _ => j) := canon_mem m hs j _ hj
    rw [gs_mul _ z _ hk, gs_constFn _ _ _ z hk, mul_left_comm]
    refine (congrArg (gs _ z _) (hs' _)).trans ((gs_mul _ z _ a₁ _ _).trans (congrArg₂ (· * ·) ?_ (h Z r z j k hj hk)))
    exact (gs_constFn (fst (Over.mk x) Xo.univ.t.G).left _ _ z a₁ a).trans (by rw [Category.assoc, hf])
  constructor
  · intro h' k
    refine fn_ext fun y hy => ?_
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB (m.φ y)
    exact (Units.mul_right_inj _).1 ((h' _ (𝟙 _) y j k hj hy).symm.trans (key _ (𝟙 _) y j k hj hy))
  · intro h' Z r z j k hj hk
    rw [h' k]
    exact key Z r z j k hj hk

theorem secTie_baseChange {th : LB.Sec t.PP.L} {s : LB.Sec (PPx x)} (h : SecTie m th s) {S' : Type} [CommRing S']
    (φ : S →+* S') {x' : Sp S' ⟶ Xo.X} {t'' : SAB H (Sp S')} (m' : SABMap t'' Xo.univ.t x')
    (n : SABMap t'' t (spMap φ)) (s' : LB.Sec (PPx x')) (w : LB.Iso t''.PP.L (t.PP.L.pull n.φ))
    (θ : LB.Sec (t.PP.L.pull n.φ)) (th' : LB.Sec t''.PP.L) (hx : x' = spMap φ ≫ x) (hφ : m'.φ = n.φ ≫ m.φ)
    (hb : SecBC φ 1 x x' s s') (hw : RigIso n w) (hθ : PullSec n.φ th θ) :
    SecTie m' th' s' ↔ IsoMaps w th' θ := by
  obtain ⟨g, hs, hf⟩ := exists_canon m
  obtain ⟨g', hs', hf'⟩ := exists_canon m'
  obtain ⟨w₁, -, hw₁, -⟩ := id h
  obtain ⟨w₂, hw₂, T⟩ := GlobalTheory.LiftBaseChange.rigIso_comp m n m' hx hφ hw₁ hw
  obtain ⟨pm, ps, pf, hp⟩ := hb
  have eg : g' ≫ pm = n.φ ≫ g := by
    apply SecCalc.pm_ext
    · rw [Category.assoc, ps, hs', Category.assoc, hs, hφ]
    · rw [Category.assoc, pf, ← Category.assoc, hf', Category.assoc, hf]
      exact n.cart.1.w.symm
  have ept : ∀ y, m'.φ y = m.φ (n.φ y) := fun y => by rw [hφ]; rfl
  rw [secTie_iff m hw₁ hs hf] at h
  rw [secTie_iff m' hw₂ hs' hf', isoMaps_iff]
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ t''.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (i : t.PP.L.ι),
      m.φ (n.φ (r z)) ∈ Xo.univ.t.PP.L.U j → n.φ (r z) ∈ t.PP.L.U i →
      gs (r ≫ g') z ((PPx x').U (fun _ => j)) (s'.f (fun _ => j)) =
        (gw w₁ (r ≫ n.φ) z j i).val * gs r z _ (θ.f (fun _ => i)) := by
    intro Z r z j i hj hi
    have a₁ : (r ≫ g') z ∈ (PPx x').U (fun _ => j) := canon_mem m' hs' j _ (by rw [ept]; exact hj)
    have le : (t.PP.L.pull n.φ).U (fun _ => i) ≤ n.φ ⁻¹ᵁ t.PP.L.U i := fun q hq => mem_pull.1 hq
    have e₁ := hp (fun _ => j) (SecCalc.ppx_le pm ps _)
    rw [SecCalc.scal_one' x (fun _ => j), _root_.one_mul] at e₁
    rw [hθ (fun _ => i) le, gs_appLE n.φ _ _ le r z (mem_pull.2 hi), ← h Z (r ≫ n.φ) z j i hj hi, ← e₁,
      gs_appLE pm _ _ _ (r ≫ g') z a₁, Category.assoc, Category.assoc, eg]
  constructor
  · intro h' Z r z i k hi hk
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB (m.φ (n.φ (r z)))
    have e := (key Z r z j i hj hi).symm.trans (h' Z r z j k (by rw [ept]; exact hj) hk)
    rw [T Z r z j i k hj hi hk, Units.val_mul, _root_.mul_assoc] at e
    exact (Units.mul_right_inj _).1 e
  · intro h' Z r z j k hj hk
    obtain ⟨i, hi⟩ := exists_chart t.PP.isLB (n.φ (r z))
    rw [ept] at hj
    rw [key Z r z j i hj hi, h' Z r z i k hi hk, T Z r z j i k hj hi hk, Units.val_mul, _root_.mul_assoc]

theorem secTie_calc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S)) (m : SABMap t' Xo.univ.t x) (th : LB.Sec t'.PP.L) (s : LB.Sec (PPx x)), SecTie m th s → (∀ (a : S) (x' : Sp S ⟶ Xo.X) (s' : LB.Sec (PPx x')) (th' : LB.Sec t'.PP.L), x' = x → SecBC (RingHom.id S) a x x' s s' → (SecTie m th' s' ↔ ∀ i, th'.f i = constFn t'.G.hom _ a * th.f i)) ∧ ∀ (S' : Type) [CommRing S'] (φ : S →+* S') (x' : Sp S' ⟶ Xo.X) (t'' : SAB H (Sp S')) (m' : SABMap t'' Xo.univ.t x') (n : SABMap t'' t' (spMap φ)) (s' : LB.Sec (PPx x')) (w : LB.Iso t''.PP.L (t'.PP.L.pull n.φ)) (θ : LB.Sec (t'.PP.L.pull n.φ)) (th' : LB.Sec t''.PP.L), x' = spMap φ ≫ x → m'.φ = n.φ ≫ m.φ → SecBC φ 1 x x' s s' → RigIso n w → PullSec n.φ th θ → (SecTie m' th' s' ↔ IsoMaps w th' θ) := by
  intro E _ _ _ H Dw l Xo S _ x t' m th s h
  refine ⟨fun a x' s' th' hx hb => ?_, fun S' _ φ x' t'' m' n s' w θ th' hx hφ hb hw hθ =>
    secTie_baseChange m h φ m' n s' w θ th' hx hφ hb hw hθ⟩
  subst hx
  have e : x' = spMap (RingHom.id S) ≫ x' := by rw [SecCalc.spMap_id', Category.id_comp]
  exact secTie_scale m h a
    (((SecCalc.sec_calc E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) x' x' x' e e).2.1 a s s').1 hb)

end GlobalTheory.LamT.TieCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingEqOfIsomorphicCubePairings
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CM

open ReciprocityTheory.ChartRestriction.G.Out DescentPairing AdjointOfPairing

variable {S : Scheme.{0}} {A B X Y : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj Y] [IsCommMonObj Y]

theorem exists_gen_lam_two (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {N : RigLB A} (cb : CubicalStr A N)
    {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (a : X ⟶ A) (g : Y ⟶ A) [IsMonHom g] (n : ℕ) (y : T ⟶ X)
    (hy : (y ≫ a) ^ n = 1) :
    ∃ t : LB.Gen (LB.LinComb N.L (fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T Y ≫ y) (snd T Y ^ n)).left ≫
        (psum A ![fst X Y ≫ a, snd X Y ≫ g] I.down).left) (fun I => (-1) ^ (2 - I.down.card))),
      t.IsGen ∧ ∀ (z : T ⟶ Y) (e : Γ(T.left, ⊤)ˣ), z ^ n = 1 → WeilIs A N.L n (y ≫ a) (z ≫ g) e →
        ∀ (p : T.left) (J), Good N.L p J →
          val t (lift (𝟙 T) z).left p J = val t (lift (𝟙 T) (1 : T ⟶ Y)).left p J * gm (𝟙 T.left) p ⊤ e := by
  obtain ⟨u₀, hu₀, v₀⟩ := exists_gen_pairing hG hA cb p₀ hT n (y ≫ a) hy
  obtain ⟨σ, hσ⟩ := exists_frame N.isLB (K := Fin 2) ![(y ≫ a).left, (1 : T ⟶ A).left] ![-1, 1] p₀ hT
  obtain ⟨u, hu, v⟩ := exists_gen N.isLB
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T Y ≫ y) (snd T Y ^ n)).left ≫
        (psum A ![fst X Y ≫ a, snd X Y ≫ g] I.down).left) (ε' := fun I => (-1) ^ (2 - I.down.card))
    (fun U _ h => by
      have e : ∀ I, (lift (fst T Y ≫ y) (snd T Y ^ n)).left ≫ (psum A ![fst X Y ≫ a, snd X Y ≫ g] I).left =
          (psum A ![fst T Y ≫ y ≫ a, (snd T Y ≫ g) ^ n] I).left := fun I => by
        refine congrArg CommaMorphism.left ((psum_hom (preHom (lift (fst T Y ≫ y) (snd T Y ^ n))) _ I).trans ?_)
        congr 1
        funext i
        fin_cases i
        · show lift _ _ ≫ fst X Y ≫ a = fst T Y ≫ y ≫ a
          rw [lift_fst_assoc, Category.assoc]
        · show lift _ _ ≫ snd X Y ≫ g = (snd T Y ≫ g) ^ n
          rw [lift_snd_assoc, MonObj.pow_comp]
      have f : ∏ i : Fin 2, h ((fst T Y).left ≫ ![(y ≫ a).left, (1 : T ⟶ A).left] i) ^ ![(-1 : ℤ), 1] i =
          (h (fst T Y ≫ y ≫ a).left)⁻¹ * h (fst T Y ≫ (1 : T ⟶ A)).left := by
        rw [Fin.prod_univ_two]
        exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
      refine (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _
        (prod_mulT n (y ≫ a) (fst T Y) (snd T Y ≫ g) h) f).trans ?_
      simp only [e]
      rw [NormRos.prod_square, MonObj.comp_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen N.L _ _ _ _ (LB.pullGen N.L _ _ u₀ (lift (fst T Y) (snd T Y ≫ g)).left)
      (LB.pullGen N.L _ _ σ (fst T Y).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _) (DVR.pullGen_isGen _ _ _ _ hσ _))
  refine ⟨u, hu, fun z e hz he p J hJ => ?_⟩
  have w : ∀ b : T ⟶ Y, val u (lift (𝟙 T) b).left p J =
      val u₀ (lift (𝟙 T) (b ≫ g)).left p J * val σ (𝟙 T :).left p J := fun b => by
    rw [v _ _ p J hJ, val_mul hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, comp_lift,
      lift_fst, lift_snd_assoc]
  have w₀ := v₀ (z ≫ g) e (by rw [← MonObj.pow_comp, hz, MonObj.one_comp]) he T (𝟙 T) 1 p J hJ
  rw [Category.id_comp, _root_.mul_one] at w₀
  rw [w, w, w₀, MonObj.one_comp, mul_right_comm]
  rfl

theorem weil_value_eq_of_lamEq (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    (hY : IsAbelianScheme Y) {N : RigLB A} {L : RigLB B} (cN : CubicalStr A N) (cL : CubicalStr B L)
    (f₁ : X ⟶ A) (f₂ : Y ⟶ A) (g₁ : X ⟶ B) (g₂ : Y ⟶ B) [IsMonHom f₂] [IsMonHom g₂]
    (H : LamEq N.L f₁ f₂ L.L g₁ g₂) {T : Over S} (p₀ : T.left) (hT : ∀ p : T.left, p = p₀) (n : ℕ) (y : T ⟶ X)
    (z : T ⟶ Y) (hf : (y ≫ f₁) ^ n = 1) (hg : (y ≫ g₁) ^ n = 1) (hz : z ^ n = 1) (e e' : Γ(T.left, ⊤)ˣ)
    (he : WeilIs B L.L n (y ≫ g₁) (z ≫ g₂) e) (he' : WeilIs A N.L n (y ≫ f₁) (z ≫ f₂) e') : e = e' := by
  refine unit_ext fun p _ => ?_
  obtain ⟨t, ht, v⟩ := exists_gen_lam_two hG hB cL p₀ hT g₁ g₂ n y hg
  obtain ⟨t', ht', v'⟩ := exists_gen_lam_two hG hA cN p₀ hT f₁ f₂ n y hf
  choose J hJ using fun χ : T.left ⟶ B.left => exists_chart L.isLB (χ p)
  choose J' hJ' using fun χ : T.left ⟶ A.left => exists_chart N.isLB (χ p)
  have r := PairingOfLam.val_ratio L.isLB N.isLB H _ t ht t' ht' (fst T Y).left (WeilCube.surj_fst hG hY T)
    (lift (𝟙 T) z).left (lift (𝟙 T) (1 : T ⟶ Y)).left
    (by rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst_assoc, lift_fst_assoc,
      MonObj.comp_pow, MonObj.comp_pow, lift_snd, lift_snd, hz, one_pow])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) p hJ hJ'
  rw [v z e hz he p J hJ, v' z e' hz he' p J' hJ'] at r
  apply Additive.ofMul.injective
  have r' := congrArg Additive.ofMul r
  simp only [ofMul_mul, ofMul_inv] at r'
  linear_combination (norm := abel) r'

theorem weilEq_of_lamEq : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (X Y A B : Out.PolAV (Sp k)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → LamEq A.L f₁ f₂ B.L g₁ g₂ → WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp k)) := by
  intro hl k _ _ _ X Y A B f₁ f₂ g₁ g₂ _ _ _ _ H n x y c _ hx hy
  haveI := A.isAb.comm
  haveI := B.isAb.comm
  haveI := Y.isAb.comm
  obtain ⟨rA, hrA⟩ := A.rigid
  obtain ⟨rB, hrB⟩ := B.rigid
  obtain ⟨⟨cA⟩, -⟩ := hl.cube _ A ⟨A.L, rA, A.isLB, hrA⟩ rfl
  obtain ⟨⟨cB⟩, -⟩ := hl.cube _ B ⟨B.L, rB, B.isLB, hrB⟩ rfl
  let T : Over (Sp k) := Over.mk (𝟙 _)
  let p₀ : T.left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)
  have hT : ∀ p : T.left, p = p₀ := fun p => Subsingleton.elim (α := PrimeSpectrum k) p p₀
  have h₁ : (x ≫ f₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have h₂ : (y ≫ f₂) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have h₃ : (x ≫ g₁) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have h₄ : (y ≫ g₂) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have key := weil_value_eq_of_lamEq hl.globalFns A.isAb B.isAb Y.isAb cA cB f₁ f₂ g₁ g₂ H p₀ hT n x y h₁ h₃ hy
  constructor
  · intro h
    obtain ⟨e, he, -⟩ := (hl.weil _ B n T).1 _ _ h₃ h₄
    exact key e _ he h ▸ he
  · intro h
    obtain ⟨e, he, -⟩ := (hl.weil _ A n T).1 _ _ h₁ h₂
    exact (key _ e h he).symm ▸ he

end GlobalTheory.CM
end
end

