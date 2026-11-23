module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0178
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegDataFiniteUnramified
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegClause

theorem lbIso_pull_pull {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X} (h : LBIso L' (L.pull φ))
    (ψ : X'' ⟶ X') : LBIso (L'.pull ψ) (L.pull (ψ ≫ φ)) :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' ψ ψ rfl) (chartPullSame L _ _ _ ψ fun _ => rfl) h

theorem lbIso_lam_pull {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (e : A ⟶ B) [IsMonHom e] {L : LB A.left} {M : LB B.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : LBIso L (M.pull e.left)) : LBIso (abelian₂ A L) ((abelian₂ B M).pull (e ⊗ₘ e).left) := by
  have pa : ∀ I : Finset (Fin 2), psum A (x2 A) I ≫ e = (e ⊗ₘ e) ≫ psum B (x2 B) I := by
    intro I
    refine (psum_hom (MonoidHom.mk' (fun z : G2 A ⟶ A => z ≫ e) fun a b => MonObj.mul_comp a b _) _ I).trans
      (Eq.trans (congrArg (fun z => psum B z I) (funext fun k => ?_)) (psum_hom (preHom (e ⊗ₘ e)) _ I).symm)
    fin_cases k
    · exact (tensorHom_fst e e).symm
    · exact (tensorHom_snd e e).symm
  have hB : (abelian₂ B M).IsLB := DVR.linComb_isLB M hM _ _
  have r : LBIso (abelian₂ B M) (abelian₂ B M) := GlobalTheory.PolBaseChange.lbIso_refl hB
  have h₁ : LBIso (abelian₂ A L) (abelian₂ A (M.pull e.left)) := GlobalTheory.PowPrimitive.lbIso_linComb h _ _
  have h₂ : LBIso (abelian₂ A (M.pull e.left)) ((abelian₂ B M).pull (e ⊗ₘ e).left) :=
    LBIso.chartPull (chartPullLinComb M e.left (K := ULift.{0} (Finset (Fin 2)))
      (fun I => (psum A (x2 A) I.down).left) (fun I => (psum B (x2 B) I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) (e ⊗ₘ e).left (fun I => congrArg (fun z => z.left) (pa I.down)))
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (abelian₂ B M) _ _ rfl) r
  exact LBIso.trans (DVR.linComb_isLB L hL _ _) (DVR.linComb_isLB _ (pull_isLB hM _) _ _) (pull_isLB hB _) h₁ h₂

end GlobalTheory.ZM.SiegClause
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueMapToThetaFamilyOpenPart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.UnivProp

set_option backward.isDefEq.respectTransparency false

variable {o : Type} [CommRing o] {g n N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}

theorem span_eq_top_of_coset {R : Type} [CommRing R] {v : Ix g (N' ^ 2) → R}
    (h : ∀ q : Ideal R, q.IsPrime → Coset n N' v q) : Ideal.span (Set.range v) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨c, hc⟩ := h m hm.isPrime 0
  exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))

theorem pt_eq_of_secCoord {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)} (Y : MMPre n N' I) {R : Type} [CommRing R]
    {x x' : Sp R ⟶ Y.MM} {v : Ix g (N' ^ 2) → R} (e : x ≫ Y.s = x' ≫ Y.s) (h : SecCoord Y.de Y.th x v)
    (h' : SecCoord Y.de Y.th x' v) : x = x' := by
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ Y.s)
  exact (Y.pts R β v (Y.loc R β x v hβ h)).unique ⟨hβ, h⟩ ⟨e.symm.trans hβ, h'⟩

theorem exists_thetaMap (hL : Out.Laws) (hL2 : Out.Laws2) (hn : 2 ≤ n) (hd : n ∣ N') (ho : Odd N') {em : o →+* ℂ}
    {C : TObj g (N' ^ 2) J b (spMap em) → Prop} (Y : MMPre n N' (thIdeal em C)) {S : Scheme.{0}} {s : S ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s) (hS : IsReduced S) (hD : Dense (fromSet em C t)) :
    ∃ f : S ⟶ Y.MM, f ≫ Y.s = s ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ S),
      ∃ v, t.HasTh y v ∧ SecCoord Y.de Y.th (y ≫ f) v := by
  classical
  have hloc := fun p : S => GlobalTheory.ThetaLocal.exists_hasTh hL hL2 o g N' J b S s t ho p
  choose R hR x v hx hp hth using hloc
  have hβ' : ∀ p, ∃ β : o →+* R p, x p ≫ s = spMap β := fun p => exists_spMap (x p ≫ s)
  choose β hβ using hβ'
  have hin : ∀ p, InMM n N' (thIdeal em C) (β p) (v p) := fun p =>
    _root_.GlobalTheory.ZM.inMM_of_dense_fromSet hL hL2 o g n N' J b em C S s t (R p) (β p) (x p) (v p) hn hd ho hS hD (hx p) (hβ p) (hth p)
  have hpt : ∀ p, ∃ y : Sp (R p) ⟶ Y.MM, y ≫ Y.s = spMap (β p) ∧ SecCoord Y.de Y.th y (v p) :=
    fun p => (Y.pts (R p) (β p) (v p) (hin p)).exists
  choose f hf using hpt
  obtain ⟨F, hF⟩ := exists_glue (fun p => Sp (R p)) x hx (fun p => ⟨p, hp p⟩) f (by
    intro i j T _ z z' hz
    obtain ⟨φ, rfl⟩ := exists_spMap z
    obtain ⟨φ', rfl⟩ := exists_spMap z'
    have h1 := _root_.GlobalTheory.hasTh_baseChange hL2 o g N' J b S s t (R i) T φ (x i) (v i) (hth i)
    have h2 := _root_.GlobalTheory.hasTh_baseChange hL2 o g N' J b S s t (R j) T φ' (x j) (v j) (hth j)
    rw [hz] at h1
    have hsp : Ideal.span (Set.range fun a => φ (v i a)) = ⊤ :=
      span_eq_top_of_coset (n := n) fun q hq => _root_.GlobalTheory.coset_of_hasTh hL hL2 o g N' J b S s t n T _ _ q hn hd h1 hq
    obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b S s t T _ _ _ h1 h2 hsp
    have c1 : SecCoord Y.de Y.th (spMap φ ≫ f i) fun a => φ' (v j a) := by
      have e : (fun a => φ' (v j a)) = fun a => (u : T) * φ (v i a) := funext fun a => hu a
      rw [e]
      exact GlobalTheory.ZM.Coord.scale (GlobalTheory.ZM.Coord.baseChange (hf i).2 φ) u
    have c2 := GlobalTheory.ZM.Coord.baseChange (hf j).2 φ'
    refine pt_eq_of_secCoord Y ?_ c1 c2
    have e := congrArg (· ≫ s) hz
    simp only [Category.assoc, hβ] at e
    simp only [Category.assoc, (hf i).1, (hf j).1]
    exact e)
  refine ⟨F, ?_, ?_⟩
  · refine hom_ext_affine _ _ fun p => ⟨Sp (R p), x p, hx p, hp p, ?_⟩
    rw [← Category.assoc, hF p, (hf p).1, hβ p]
  · intro K _ y
    obtain ⟨p, hyp⟩ : ∃ p, p ∈ Set.range y := ⟨_, IsLocalRing.closedPoint K, rfl⟩
    have := hx p
    obtain ⟨z, hz⟩ := exists_lift_field (x p) y hyp (hp p)
    obtain ⟨φ, rfl⟩ := exists_spMap z
    subst hz
    refine ⟨fun a => φ (v p a), ?_, ?_⟩
    · exact _root_.GlobalTheory.hasTh_baseChange hL2 o g N' J b S s t (R p) K φ (x p) (v p) (hth p)
    · rw [Category.assoc, hF]
      exact GlobalTheory.ZM.Coord.baseChange (hf p).2 φ

private theorem exists_tObj_transport_of_eq {o₁ : Type} [CommRing o₁] {g₁ k₁ : ℕ} {J₁ : Type} {b₁ : TBase o₁ k₁}
    {S₁ : Scheme.{0}} {s₁ s₂ : S₁ ⟶ Sp o₁} (h : s₁ = s₂) (u : TObj g₁ k₁ J₁ b₁ s₁) :
    ∃ u' : TObj g₁ k₁ J₁ b₁ s₂, ∀ P : ∀ s : S₁ ⟶ Sp o₁, TObj g₁ k₁ J₁ b₁ s → Prop, P s₁ u → P s₂ u' := by
  subst h
  exact ⟨u, fun _ hP => hP⟩

theorem existsUnique_map_of_wFam : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (F : WFam n em C Mat κ) (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → t.FibShape Mat κ → ∃! f : S ⟶ F.U.toScheme, f ≫ F.U.ι ≫ F.Y.s = s' ∧ TMap t F.univ f := by
  intro hL hL2 g J _ Mat κ n w w' hnp hno
  refine ⟨2, fun j hj o _ b em C d _ _ F S s' t hS hD hFib => ?_⟩
  have hn : 2 ≤ n := hnp.two_le
  have hd : n ∣ n ^ j := dvd_pow_self n (by omega)
  have hd2 : n ^ 2 ∣ n ^ j := pow_dvd_pow n hj
  have ho : Odd (n ^ j) := hno.pow
  obtain ⟨f0, hf0s, hf0⟩ := exists_thetaMap hL hL2 hn hd ho F.Y t hS hD
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) (u : TObj g ((n ^ j) ^ 2) J b (y ≫ s')),
      TMap u t y → ∃ x' : Sp K ⟶ F.U.toScheme, x' ≫ F.U.ι = y ≫ f0 ∧ TMap u F.univ x' := by
    intro K _ _ y u hu
    obtain ⟨v, hvt, hvs⟩ := hf0 K y
    have hsh := hFib K y u hu
    have hth : u.HasTh (𝟙 _) v :=
      (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b S s' t (Sp K) (y ≫ s') u y K (𝟙 _) v hu).2 (by simpa using hvt)
    obtain ⟨u', hu'⟩ := exists_tObj_transport_of_eq (show y ≫ s' = (y ≫ f0) ≫ F.Y.s by rw [Category.assoc, hf0s]) u
    obtain ⟨h1, h2, h3⟩ := hu' (fun _ w => w.Shape Mat κ ∧ w.HasTh (𝟙 _) v ∧
      ∀ x' : Sp K ⟶ F.U.toScheme, TMap w F.univ x' → TMap u F.univ x') ⟨hsh, hth, fun _ h => h⟩
    obtain ⟨x', hx'1, hx'2⟩ := F.obj K (y ≫ f0) u' v h1 h2 hvs
    exact ⟨x', hx'1, h3 x' hx'2⟩
  have hrange : Set.range f0 ⊆ Set.range F.U.ι := by
    rintro q ⟨p, rfl⟩
    obtain ⟨K, _, _, y, p0, hp0⟩ := exists_geomPt S p
    obtain ⟨u, hu⟩ := GlobalTheory.tObj_pull o g _ J b S (Sp K) s' (y ≫ s') y t rfl
    obtain ⟨x', hx', -⟩ := key K y u hu
    refine ⟨x' p0, ?_⟩
    rw [← hp0, ← Scheme.Hom.comp_apply, hx', Scheme.Hom.comp_apply]
  set f := IsOpenImmersion.lift F.U.ι f0 hrange with hfdef
  have hfι : f ≫ F.U.ι = f0 := IsOpenImmersion.lift_fac _ _ _
  have hfs : f ≫ F.U.ι ≫ F.Y.s = s' := by rw [← Category.assoc, hfι, hf0s]
  have hmap : ∀ f' : S ⟶ F.U.toScheme, f' ≫ F.U.ι ≫ F.Y.s = s' → TMap t F.univ f' → ∀ (R : Type) [CommRing R]
      (x : Sp R ⟶ S) (v : Ix g ((n ^ j) ^ 2) → R), t.HasTh x v → SecCoord F.Y.de F.Y.th ((x ≫ f') ≫ F.U.ι) v :=
    fun f' _ hT R _ x v hth =>
      (F.th R (x ≫ f') v).1 ((GlobalTheory.hasTh_iff_of_tmap o g _ J b F.U.toScheme _ F.univ S s' t f' R x v hT).1 hth)
  have hT : TMap t F.univ f := by
    obtain ⟨t2, ht2⟩ := GlobalTheory.tObj_pull o g _ J b F.U.toScheme S (F.U.ι ≫ F.Y.s) s' f F.univ hfs
    have := hS
    have hid : TMap t t2 (𝟙 S) := by
      refine tMap_id_of_geomPt hL hL2 hn hd2 ho fun K _ _ y u hu => ?_
      obtain ⟨x', hx', hxu⟩ := key K y u hu
      have e : x' = y ≫ f := by rw [← cancel_mono F.U.ι, hx', Category.assoc, hfι]
      rw [e] at hxu
      exact TMap.cancel ht2 hxu
    simpa using TMap.comp hid ht2
  refine ⟨f, ⟨hfs, hT⟩, ?_⟩
  rintro f' ⟨hf's, hf'T⟩
  refine hom_ext_affine _ _ fun p => ?_
  obtain ⟨R, _, x, v, hx, hp, hth⟩ := GlobalTheory.ThetaLocal.exists_hasTh hL hL2 o g (n ^ j) J b S s' t ho p
  refine ⟨Sp R, x, hx, hp, (cancel_mono F.U.ι).1 ?_⟩
  refine pt_eq_of_secCoord F.Y ?_ (hmap f' hf's hf'T R x v hth) (hmap f hfs hT R x v hth)
  simp only [Category.assoc, hf's, hfs]

end GlobalTheory.ZM.UnivProp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsDimSymmetricAmplePowEqMulPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.SymAmpleCount

theorem eq_of_scaling {h : ℕ → ℕ} {g q : ℕ} {v : ℝ} (hq : 2 ≤ q)
    (hs : ∀ e, 1 ≤ e → h (e * q) = q ^ g * h e)
    (ht : Filter.Tendsto (fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) Filter.atTop (nhds v)) {e : ℕ} (he : 1 ≤ e) :
    (h e : ℝ) = v * (e : ℝ) ^ g := by
  have h₁ : ∀ i, h (e * q ^ i) = (q ^ i) ^ g * h e := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ← Nat.mul_assoc, hs _ (Nat.mul_pos he (by positivity)), ih, mul_pow]
      ring
  have h₂ : Filter.Tendsto (fun i : ℕ => e * q ^ i) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun i => Nat.le_mul_of_pos_left _ he) (tendsto_pow_atTop_atTop_of_one_lt hq)
  have he' : (e : ℝ) ^ g ≠ 0 := by positivity
  have h₃ : ((fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) ∘ fun i : ℕ => e * q ^ i) =
      fun _ => (h e : ℝ) / (e : ℝ) ^ g := by
    funext i
    have : ((q : ℝ) ^ i) ^ g ≠ 0 := by positivity
    simp only [Function.comp, h₁]
    push_cast
    rw [mul_pow]
    field_simp
  have h₄ := ht.comp h₂
  rw [h₃] at h₄
  rw [← tendsto_nhds_unique tendsto_const_nhds h₄]
  field_simp

theorem exists_two_le_cast_ne_zero (K : Type) [Field K] : ∃ l : ℕ, 2 ≤ l ∧ (l : K) ≠ 0 := by
  by_cases h : ((2 : ℕ) : K) = 0
  · refine ⟨3, by norm_num, ?_⟩
    rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_add, h]
    simp
  · exact ⟨2, le_rfl, h⟩

theorem isIso_translation {S : Scheme.{0}} (A : Over S) [GrpObj A] (x : 𝟙_ (Over S) ⟶ A) :
    IsIso ((toUnit A ≫ x) * 𝟙 A) := by
  refine ⟨(toUnit A ≫ x)⁻¹ * 𝟙 A, ?_, ?_⟩
  · rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit, Category.comp_id, inv_mul_cancel_left]
  · rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv_cancel_left]

theorem sectionsDim_symmetricAmple_pow_sq (hL : Out.Laws) (hL' : Out.Laws2) (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K))
    (M : LB P.A.left) (hM : M.IsLB) (ha : Out.RelAmple P.A M) (hs : SymB M) {k : ℕ} (hk : (k : K) ≠ 0) {r : ℕ}
    (hr : SectionsHaveFiniteDimension P.A.hom M r) : SectionsHaveFiniteDimension P.A.hom (lbPow M (k ^ 2)) (k ^ (2 * P.g) * r) := by
  refine ((_root_.GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ P.A.hom _ (LB.isLB_pull hM _)).2.1 _ (GlobalTheory.isLB_lbPow hM _)
    (_root_.GlobalTheory.MulSym.lbIso_mulPull_of_symB K P M k hM hs)).1 _ (GlobalTheory.T.sectionsHaveFiniteDimension_lbDiv_linComb hL hL' K P M k r hM hk fun y _ => ?_)
  obtain ⟨x, hx⟩ := GlobalTheory.T.twist_ampleBundle_translationBundle_iso_translate hL hL' K P M y hM ha
  refine ((_root_.GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ P.A.hom _ (LB.isLB_pull hM _)).2.1 _
    (LB.isLB_div hM (LB.isLB_linComb P.isLB _ _)) hx.symm).1 _ ?_
  have := isIso_translation P.A x
  have H := ((_root_.GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ P.A.hom M hM).2.2.2.2.2 _
    ((Over.forget _).mapIso (asIso ((toUnit P.A ≫ x) * 𝟙 P.A))) r).1 hr
  have e : ((Over.forget _).mapIso (asIso ((toUnit P.A ≫ x) * 𝟙 P.A))).hom ≫ P.A.hom = P.A.hom := Over.w _
  exact (congrArg (fun q => SectionsHaveFiniteDimension q _ r) e).mp H

end GlobalTheory.SymAmpleCount

namespace GlobalTheory

theorem sectionsDim_symmetricAmple_pow_eq_mul_pow : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left), M.IsLB → Out.RelAmple P.A M → SymB M → ∃ δ : ℕ, 1 ≤ δ ∧ Vol P.A.hom M P.g δ ∧ ∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow M e) (δ * e ^ P.g) := by
  intro hL hL' K _ _ P M hM ha hs
  obtain ⟨v, hv, h, hh, ht⟩ := _root_.GlobalTheory.VolEx.exists_vol hL hL' K P M hM ha
  obtain ⟨l, hl, hlK⟩ := SymAmpleCount.exists_two_le_cast_ne_zero K
  have B := _root_.GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ P.A.hom M hM
  have sc : ∀ e, 1 ≤ e → h (e * l ^ 2) = (l ^ 2) ^ P.g * h e := fun e he => by
    have hMe := GlobalTheory.isLB_lbPow hM e
    have hae : Out.RelAmple P.A (lbPow M e) :=
      (GlobalTheory.relAmple_finite_pow_iso _ P.A P.A (𝟙 _) M e he P.isAb P.isAb hM
        (inferInstanceAs (IsFinite (𝟙 P.A.left)))).2.1.2 ha
    have hse : SymB (lbPow M e) :=
      LBIso.trans hMe (GlobalTheory.isLB_lbPow (LB.isLB_pull hM _) e) (LB.isLB_pull hMe _)
        ((B.2.1 _ (LB.isLB_pull hM _) hs).2 e) (B.2.2.2.2.1 _ _ e)
    have H := SymAmpleCount.sectionsDim_symmetricAmple_pow_sq hL hL' K P _ hMe hae hse hlK (hh e)
    have H' := ((_root_.GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ P.A.hom _ (GlobalTheory.isLB_lbPow hMe _)).2.1 _ (GlobalTheory.isLB_lbPow hM _)
      (B.2.2.1 e (l ^ 2))).1 _ H
    rw [← pow_mul]
    exact (_root_.GlobalTheory.SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ P.A.hom _ (GlobalTheory.isLB_lbPow hM _)).1 _ _ (hh _) H'
  have key : ∀ e, 1 ≤ e → (h e : ℝ) = v * (e : ℝ) ^ P.g := fun e he =>
    SymAmpleCount.eq_of_scaling (q := l ^ 2) (by nlinarith) sc ht he
  have h₁ : (h 1 : ℝ) = v := by simpa using key 1 le_rfl
  refine ⟨h 1, ?_, ⟨h, hh, h₁ ▸ ht⟩, fun e he => ?_⟩
  · have : (0 : ℝ) < h 1 := h₁ ▸ hv
    exact_mod_cast this
  · have : h e = h 1 * e ^ P.g := by
      have := key e he
      rw [← h₁] at this
      exact_mod_cast this
    exact this ▸ hh e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaFamIsPEL
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem GlobalTheory.thetaFam_isPEL : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (n N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∀ F : ThetaFam n em (PELClass (b := b) D a bas ρ em), ∃ τ : SAB H F.MM, IsPEL D a bas ρ F.univ τ := by
  intro h1 h2 h3 E _ _ _ H D g J _ a w w' bas hpq hbas hw hw' hcl n N' o _ b em ρ hρ hem F
  obtain ⟨hded, -, hinj⟩ := hem
  have := F.reduced
  have : LocallyOfFiniteType F.s := by
    obtain ⟨N, i, hi, -, hs⟩ := F.qproj
    have := isProper_str o N
    rw [← hs]
    infer_instance
  have : IsLocallyNoetherian F.MM := LocallyOfFiniteType.isLocallyNoetherian F.s
  exact GlobalTheory.T.exists_isPELTriple_of_dense_fibres h1 h2 h3 E H D g J a bas w w' hpq hbas hw hw' hcl (N' ^ 2) o b em ρ F.MM F.s F.univ hρ hinj F.dense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapeOfGenericPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ShapeGeneric

section Bundles

variable {X X' Y Y' : Scheme.{0}}

theorem iso_linComb_pull {L : LB X} {L' : LB X'} {F : X' ⟶ X} (H : LBIso L' (L.pull F)) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (e : ∀ k, ψ' k ≫ F = h ≫ ψ k) :
    LBIso (LB.LinComb L' ψ' ε) ((LB.LinComb L ψ ε).pull h) := by
  obtain ⟨w, hw⟩ := H
  exact LBIso.chartPull (chartPullId _) (chartPullOut L ψ ε h _ e) (iso_linComb ((isGen_iff w).1 hw) ψ' ε)

end Bundles

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
  (h : IsGrpPullback G' G f φ)

variable {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T)

theorem push_linComb {n : ℕ} {x' : Fin n → (T' ⟶ G')} {x : Fin n → (T ⟶ G)} (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i)
    (a : Fin n → ℕ) : pushPt h.1.w (Out.linComb x' a) = U ≫ Out.linComb x a := by
  refine (map_list_prod (pushHom h T') _).trans (Eq.trans ?_ (map_list_prod (preHom (G := G) U) _).symm)
  rw [List.map_ofFn, List.map_ofFn]
  refine congrArg (fun z => (List.ofFn z).prod) (funext fun i => ?_)
  exact (map_pow (pushHom h T') _ _).trans ((congrArg (· ^ a i) (hx i)).trans (map_pow (preHom (G := G) U) _ _).symm)

theorem push_comp {x' : T' ⟶ G'} {x : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) {a' : G' ⟶ G'} {a : G ⟶ G}
    (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w (x' ≫ a') = U ≫ x ≫ a := by
  rw [← Category.assoc, ← hx]
  refine Over.OverMorphism.ext ?_
  show (x'.left ≫ _) ≫ _ = (x'.left ≫ _) ≫ _
  rw [Category.assoc, ha, Category.assoc]

end Group

def baseMap {S S' : Scheme.{0}} (f : S' ⟶ S) : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S :=
  Over.homMk f ((Category.comp_id _).trans (Category.id_comp _).symm)

end GlobalTheory.ShapeGeneric

namespace GlobalTheory

open ShapeGeneric

theorem relAmple_chosen_pullback {S S' : Scheme.{0}} {A : Over S} [IsProper A.hom] {A' : Over S'} {x : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (H : IsPullback φ A'.hom A.hom x) {M : LB A.left} {M' : LB A'.left} (hM : M.IsLB)
    (hM' : M'.IsLB) (a : LBIso M' (M.pull φ)) (c : Out.RelAmple A' M') :
    Out.RelAmple ((Over.pullback x).obj A) (M.pull (pullback.fst A.hom x)) := by
  have : IsProper A'.hom := MorphismProperty.of_isPullback (P := @IsProper) H ‹_›
  have P : IsPullback (pullback.fst A.hom x) (pullback.snd A.hom x) A.hom (𝟙 S' ≫ x) :=
    (Category.id_comp x).symm ▸ IsPullback.of_hasPullback A.hom x
  let ψ : pullback A.hom x ⟶ A'.left := H.lift (pullback.fst _ _) (pullback.snd _ _ ≫ 𝟙 S')
    (P.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ φ = pullback.fst _ _ := H.lift_fst _ _ _
  have Q : IsPullback ψ (pullback.snd A.hom x) A'.hom (𝟙 S') :=
    IsPullback.of_right (hψ ▸ P) (H.lift_snd _ _ _) H
  have R := AmpleBaseChange.relAmple_of_isPullback hM' c Q
  have e : LBIso (M'.pull ψ) (M.pull (pullback.fst A.hom x)) :=
    a.chartPull (GlobalTheory.chartPullPull M' ψ) (chartPullSame M _ _ _ ψ fun _ => hψ.symm)
  have pr : IsProper (Over.mk (pullback.snd A.hom x)).hom := inferInstanceAs (IsProper (pullback.snd A.hom x))
  have h₁ := LB.isLB_pull hM' ψ
  have h₂ := LB.isLB_pull hM (pullback.fst A.hom x)
  exact (relAmple_iff_isAmpleLB (Over.mk (pullback.snd A.hom x)) h₂).2 fun U hU =>
    ((relAmple_iff_isAmpleLB (Over.mk (pullback.snd A.hom x)) h₁).1 R U hU).of_lbIso (LB.isLB_pull h₂ _)
      (LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) e.symm)

theorem shape_of_generic : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) Mat κ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsIntegral S] (s : S ⟶ Sp o) (t : TObj g k J b s) (K : Type) [Field K] (x : Sp K ⟶ S) (s' : Sp K ⟶ Sp o) (tK : TObj g k J b s'), Set.range x = {genericPoint S} → TMap tK t x → tK.Shape Mat κ → t.Shape Mat κ := by
  intro l₁ l₂ o _ g k J b Mat κ S _ _ s t K _ x s' t' hx ⟨φ, h, hL, hpt, hact⟩ H j
  have := t.ab.proper
  have dom : IsDominant x := ⟨by
    rw [DenseRange, hx]
    exact dense_iff_closure_eq.2 (genericPoint_closure S)⟩
  have lb : ∀ {X Y : Scheme.{0}} {L : LB X} (_ : L.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ),
      (LB.LinComb L ψ ε).IsLB := fun hL _ _ _ _ => DVR.linComb_isLB _ hL _ _
  have pt : ∀ i, pushPt h.1.w (t'.pt i) = baseMap x ≫ t.pt i := fun i => Over.OverMorphism.ext (hpt i)
  have p₁ := fun i => push_comp h _ (pt i) (hact j)
  have p₂ : ∀ a, pushPt h.1.w (t'.lab a) = baseMap x ≫ t.lab a := fun a => push_linComb h _ pt _
  have i₁ : LBIso (LB.LinComb t'.L (K := Fin 2) ![𝟙 t'.A.left, (t'.act j).left] ![(κ : ℤ), -1])
      ((LB.LinComb t.L (K := Fin 2) ![𝟙 t.A.left, (t.act j).left] ![(κ : ℤ), -1]).pull φ) :=
    iso_linComb_pull hL _ _ _ φ fun i => by
      fin_cases i
      exacts [(Category.id_comp _).trans (Category.comp_id _).symm, hact j]
  refine ⟨fun i => ?_, GlobalTheory.AmpleSpecialisation.relAmple_of_genericFibre l₁ l₂ S t.pol _ K x (lb t.isLB _ _) hx
    (relAmple_chosen_pullback h.1 (lb t.isLB _ _) (lb t'.isLB _ _) i₁ (H j).2)⟩
  have e := (p₁ i).symm.trans (((H j).1 i).symm ▸ p₂ _)
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := S) t.A.hom ?_ x
    (congrArg (fun q => q.left) e))
  exact (Over.w _).trans (Over.w _).symm

end GlobalTheory
end
end

