module

public import Mathlib
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0313
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0377
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0321
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
section
set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin

section Abstract

variable {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R)
  {V : Type} [AddCommGroup V] [Module R V]

structure IsHermRing : Prop where
  invol : ∀ a, c (c a) = a
  conj_mem : ∀ a ∈ 𝔬, c a ∈ 𝔬
  nontrivial : Nontrivial R
  artinian : IsArtinianRing R
  noeth : IsNoetherianRing 𝔬
  two : IsUnit (2 : R)
  denom : ∀ a : R, ∃ s ∈ 𝔬, IsUnit s ∧ s * a ∈ 𝔬
  principal : ∀ I : Submodule 𝔬 R, I.FG → (∃ u ∈ I, IsUnit u) → ∃ u : R, IsUnit u ∧ I = Submodule.span 𝔬 {u}

structure IsHerm (h : V → V → R) : Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (a : R) (x y : V), h x (a • y) = a * h x y
  symm : ∀ x y, h y x = c (h x y)

structure IsPerfect (h : V → V → R) : Prop where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0
  repr : ∀ f : V →ₗ[R] R, ∃ x, ∀ y, h x y = f y

def IsLat (L : Submodule 𝔬 V) : Prop :=
  L.FG ∧ Submodule.span R (L : Set V) = ⊤

def IsEvenInt (h : V → V → R) (L : Submodule 𝔬 V) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, h x y ∈ 𝔬) ∧ ∀ x ∈ L, ∃ a ∈ 𝔬, h x x = a + c a

def IsMaxEven (h : V → V → R) (L : Submodule 𝔬 V) : Prop :=
  IsLat 𝔬 L ∧ IsEvenInt c 𝔬 h L ∧ ∀ L' : Submodule 𝔬 V, IsEvenInt c 𝔬 h L' → L ≤ L' → L' ≤ L

structure IsFrame {r : ℕ} (h : V → V → R) (x y : Fin r → V) : Prop where
  xx : ∀ i j, h (x i) (x j) = 0
  yy : ∀ i j, h (y i) (y j) = 0
  xy : ∀ i j, h (x i) (y j) = if i = j then 1 else 0

def IsIsomOnto (h : V → V → R) (p : V ≃ₗ[R] V) (L L' : Submodule 𝔬 V) : Prop :=
  (∀ x y, h (p x) (p y) = h x y) ∧ ∀ z, z ∈ L ↔ p z ∈ L'

def HasBase : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module R V] [Module.Finite R V] (h : V → V → R), IsHerm c h → IsPerfect h →
    (∀ x y, h x x = 0 → h x y ≠ 1) → ∀ L L' : Submodule 𝔬 V, IsMaxEven c 𝔬 h L → IsMaxEven c 𝔬 h L' →
      ∃ p : V ≃ₗ[R] V, IsIsomOnto 𝔬 h p L L'

def FlagTransitive : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module R V] [Module.Finite R V] (h : V → V → R), IsHerm c h → IsPerfect h →
    ∀ (r : ℕ) (x y : Fin r → V), IsFrame h x y → ∀ L L' : Submodule 𝔬 V, IsMaxEven c 𝔬 h L → IsMaxEven c 𝔬 h L' →
      ∃ p : V ≃ₗ[R] V, IsIsomOnto 𝔬 h p L L' ∧
        ∀ j, p (x j) ∈ Submodule.span R (x '' {i | i ≤ j})

def IsAdapted {r : ℕ} (h : V → V → R) (x y : Fin r → V) (L : Submodule 𝔬 V) : Prop :=
  ∀ z, z ∈ L ↔ (∀ i, h (x i) z ∈ 𝔬) ∧ (∀ i, h (y i) z ∈ 𝔬) ∧
    z - ∑ i, h (y i) z • x i - ∑ i, h (x i) z • y i ∈ L

end Abstract

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def colV (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin r) E) (i : Fin r) : Fin n → Fv F v ⊗[F] E :=
  fun a => inclR (F := F) (Fv F v) (X a i)

def stabLat {v : HeightOneSpectrum (𝓞 F)} (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)) :
    Subgroup (GLoc σ J v) where
  carrier := {g | ∀ y, y ∈ Λ ↔ (matHom _ σ J g).1 *ᵥ y ∈ Λ}
  one_mem' := fun y => by simp
  mul_mem' := fun {a b} ha hb y => by
    rw [hb y, ha, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  inv_mem' := fun {a} ha y => by
    rw [ha ((matHom _ σ J a⁻¹).1 *ᵥ y), Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
    simp

theorem mem_stabLat {v : HeightOneSpectrum (𝓞 F)} {Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)}
    {g : GLoc σ J v} : g ∈ stabLat σ J Λ ↔ ∀ y, y ∈ Λ ↔ (matHom _ σ J g).1 *ᵥ y ∈ Λ := Iff.rfl

def leviMat (A : Type) [CommRing A] [Algebra F A] (X Y : Matrix (Fin n) (Fin r) E)
    (M : Matrix (Fin n) (Fin n) (A ⊗[F] E)) : Matrix (Fin n) (Fin n) (A ⊗[F] E) :=
  let Xa := X.map (inclR (F := F) A)
  let Ya := Y.map (inclR (F := F) A)
  let Xd := (cT (σ : E →+* E) X * J).map (inclR (F := F) A)
  let Yd := (cT (σ : E →+* E) Y * J).map (inclR (F := F) A)
  let P := 1 - Xa * Yd - Ya * Xd
  Xa * diagonal (fun i => (Yd * M * Xa) i i) * Yd + Ya * diagonal (fun i => (Xd * M * Ya) i i) * Xd + P * M * P

end Place

end GlobalTheory.CompanionTheory.KFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetVectorLiftDominant
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.CassPush

section SlopeTestRemainingChoices

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pi_mul (π : Representation ℂ G V) (a b : G) (v : V) : π a (π b v) = π (a * b) v := by
  rw [map_mul, Module.End.mul_apply]

theorem mem_fixed_iff (π : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed π H ↔ ∀ h ∈ H, π h v = v := by
  constructor
  · intro hv h hh
    have h1 : ∀ h : H, π (h : G) v = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • v := hv
    simpa using h1 ⟨h, hh⟩
  · intro hv
    show ∀ h : H, π (h : G) v = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • v
    intro h
    simpa using hv h h.2

theorem mkQ_avg (W : Submodule ℂ V) (r : ℕ) (hr : 0 < r) (f : Fin r → V) (m : V ⧸ W)
    (h : ∀ i, W.mkQ (f i) = m) : W.mkQ (((r : ℂ)⁻¹) • ∑ i, f i) = m := by
  have hr' : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum, Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hr', one_smul]

end SlopeTestRemainingChoices

section Avg

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_avg (K : Subgroup G) (hK : IsCompact (K : Set G)) (π : Representation ℂ G V)
    (hπ : IsSmooth π) (E : V →ₗ[ℂ] V)
    (hE : ∀ (u : V) (H : Subgroup G), H ≤ K → (∀ h ∈ H, π h u = u) → ∀ (r : ℕ) (x : Fin r → G),
      0 < r → (∀ i, x i ∈ K) → (∀ y ∈ K, ∃! i, (x i)⁻¹ * y ∈ H) →
      E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u)
    (u : V) (A : Subgroup G) (hA : A ≤ K) (hc : ∀ y ∈ K, ∃ a ∈ A, π (a⁻¹ * y) u = u) :
    ∃ (r : ℕ) (x : Fin r → G), 0 < r ∧ (∀ i, x i ∈ A) ∧
      E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let H' : Subgroup K :=
    { carrier := {g | π (g : G) u = u}
      mul_mem' := by
        intro a b ha hb
        show π ((a * b : K) : G) u = u
        rw [Subgroup.coe_mul, ← pi_mul, show π (b : G) u = u from hb, show π (a : G) u = u from ha]
      one_mem' := by
        show π ((1 : K) : G) u = u
        simp
      inv_mem' := by
        intro a ha
        show π ((a⁻¹ : K) : G) u = u
        have ha' : π (a : G) u = u := ha
        conv_lhs => rw [← ha']
        rw [pi_mul]
        simp }
  have hH' : IsOpen (H' : Set K) := (hπ u).preimage continuous_subtype_val
  have hcomp : IsCompact (((⊤ : Subgroup K)) : Set K) := by
    simpa using (isCompact_univ : IsCompact (Set.univ : Set K))
  obtain ⟨r, hr, x, hxA, hx⟩ := GlobalTheory.T.compact_group_finite_coset_reps K ⊤ H' (A.subgroupOf K) hcomp hH' le_top le_top (by
    intro y _
    obtain ⟨a, ha, hau⟩ := hc y y.2
    refine ⟨⟨a, hA ha⟩, Subgroup.mem_subgroupOf.2 ha, ?_⟩
    show π (((⟨a, hA ha⟩ : K)⁻¹ * y : K) : G) u = u
    simpa using hau)
  refine ⟨r, fun i => (x i : G), hr, fun i => Subgroup.mem_subgroupOf.1 (hxA i),
    hE u (H'.map K.subtype) ?_ ?_ r _ hr (fun i => (x i).2) ?_⟩
  · rintro _ ⟨g, _, rfl⟩
    exact g.2
  · rintro _ ⟨g, hg, rfl⟩
    exact hg
  · intro y hy
    obtain ⟨i, hi, huniq⟩ := hx ⟨y, hy⟩ trivial
    refine ⟨i, ⟨(x i)⁻¹ * ⟨y, hy⟩, hi, by simp⟩, ?_⟩
    rintro i' ⟨g, hg, e⟩
    refine huniq i' ?_
    have : (x i')⁻¹ * ⟨y, hy⟩ = g := by
      apply Subtype.ext
      simpa using e.symm
    show (x i')⁻¹ * ⟨y, hy⟩ ∈ H'
    rw [this]
    exact hg

end Avg

section Dom

variable {G : Type} [Group G] [TopologicalSpace G]

theorem conj_pow_mem (D : CassData G) (t : D.T) (hd : D.IsDom t) (j : ℕ) :
    ∀ b ∈ D.J ⊓ D.T, ((t : G) ^ j)⁻¹ * b * (t : G) ^ j ∈ D.J ⊓ D.T := by
  induction j with
  | zero => intro b hb; simpa using hb
  | succ j ih =>
    intro b hb
    have h := (hd.2.2 _ (ih b hb)).2
    have e : ((t : G) ^ (j + 1))⁻¹ * b * (t : G) ^ (j + 1)
        = (t : G)⁻¹ * (((t : G) ^ j)⁻¹ * b * (t : G) ^ j) * (t : G) := by
      rw [pow_succ]; group
    rw [e]
    exact h

end Dom

theorem exists_fixed_proj_eq_piN_pow : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : PositivityTheory.SphericalProduct.CassData G), ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ t : D.T, D.IsStrDom t → ∀ w ∈ fixed (D.piN π) D.JT, ∃ j : ℕ, ∃ v : fixed π D.J, D.proj π (v : V) = D.piN π (t ^ j) w := by
  intro G _ _ _ D V _ _ π hπ t ht w hw
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨hd, -, hsh⟩ := ht
  obtain ⟨j, hj⟩ := hsh {g | π g u = u} (hπ u) (by simp)
  have hwT := (mem_fixed_iff _ _ _).1 hw
  have hKc : IsCompact ((D.J ⊓ D.T : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact D.isCompact_J.inter_right D.isClosed_alt
  have hN : ∀ n ∈ D.N, ∀ v : V,
      (twKer π D.N 1).mkQ (π n v) = (twKer π D.N 1).mkQ v := by
    intro n hn v
    refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨n, hn⟩, v, by simp⟩)

  obtain ⟨x, hxdef⟩ : ∃ x, x = π ((t : G) ^ j) u := ⟨_, rfl⟩
  have hxNm : ∀ n ∈ D.J ⊓ D.Nm, π n x = x := by
    intro n hn
    have h1 : π (((t : G) ^ j)⁻¹ * n * (t : G) ^ j) u = u := hj n hn
    rw [hxdef]
    conv_rhs => rw [← h1]
    rw [pi_mul, pi_mul]
    congr 2
    group

  obtain ⟨E1, hE1fix, -, -, -, hE1⟩ := _root_.GlobalTheory.CompanionTheory.CompactAvg.exists_average G (D.J ⊓ D.T) hKc V π hπ
  obtain ⟨r, b, hr, hb, hy⟩ := exists_avg (D.J ⊓ D.T) hKc π hπ E1 hE1 x (D.J ⊓ D.T) le_rfl
    (fun y hy => ⟨y, hy, by simp⟩)
  obtain ⟨y, hydef⟩ : ∃ y, y = E1 x := ⟨_, rfl⟩
  rw [← hydef] at hy
  have hyK : ∀ k ∈ D.J ⊓ D.T, π k y = y := by
    rw [hydef]
    exact (mem_fixed_iff _ _ _).1 (hE1fix x)
  have hyNm : ∀ n ∈ D.J ⊓ D.Nm, π n y = y := by
    intro n hn
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hbi := hb i
    have hn' : (b i)⁻¹ * n * b i ∈ D.J ⊓ D.Nm := by
      refine ⟨D.J.mul_mem (D.J.mul_mem (inv_mem hbi.1) hn.1) hbi.1, ?_⟩
      have h2 := (Subgroup.mem_normalizer_iff.1 (D.norm_Nm _ (inv_mem hbi.2)) n).1 hn.2
      simpa using h2
    have h3 := hxNm _ hn'
    conv_rhs => rw [← h3]
    rw [pi_mul, pi_mul]
    congr 2
    group
  have hmk : (twKer π D.N 1).mkQ y = D.piN π (t ^ j) (Submodule.Quotient.mk u) := by
    rw [hy]
    refine mkQ_avg _ r hr _ _ fun i => ?_
    have hc := conj_pow_mem D t hd j (b i) (hb i)
    have hfix := hwT ⟨_, hc.2⟩ hc.1
    have h4 : π (b i) x = π ((t : G) ^ j) (π (((t : G) ^ j)⁻¹ * b i * (t : G) ^ j) u) := by
      rw [hxdef, pi_mul, pi_mul]
      congr 2
      group
    rw [h4]
    have h5 : (twKer π D.N 1).mkQ (π (((t : G) ^ j)⁻¹ * b i * (t : G) ^ j) u)
        = Submodule.Quotient.mk u := hfix
    have h6 : ∀ m : V, (twKer π D.N 1).mkQ (π ((t : G) ^ j) m)
        = D.piN π (t ^ j) ((twKer π D.N 1).mkQ m) := by
      intro m
      have : (((t ^ j : D.T)) : G) = (t : G) ^ j := by simp
      rw [← this]
      rfl
    rw [h6, h5]

  obtain ⟨E2, hE2fix, -, -, -, hE2⟩ := _root_.GlobalTheory.CompanionTheory.CompactAvg.exists_average G D.J D.isCompact_J V π hπ
  obtain ⟨r2, c, hr2, hc, hv⟩ := exists_avg D.J D.isCompact_J π hπ E2 hE2 y (D.J ⊓ D.N) inf_le_left
    (fun g hg => by
      obtain ⟨c, hc, b', hb', a, ha, rfl⟩ := D.fact_up g hg
      refine ⟨c, hc, ?_⟩
      have e : c⁻¹ * (c * b' * a) = b' * a := by group
      rw [e, ← pi_mul, hyNm a ha, hyK b' hb'])
  refine ⟨j, ⟨E2 y, hE2fix y⟩, ?_⟩
  show (twKer π D.N 1).mkQ (E2 y) = _
  rw [hv]
  refine mkQ_avg _ r2 hr2 _ _ fun i => ?_
  rw [hN _ (hc i).2, hmk]

end GlobalTheory.CompanionTheory.CassPush
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductLocalGlobal
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.Right

variable {K : Type} [Field K]

theorem inU_pre (hs : SiteLaws) {Z Y : Scheme.{0}} {p : Z ⟶ Spec (CommRingCat.of K)} {r : Y ⟶ Spec (CommRingCat.of K)}
    (u : Y ⟶ Z) (hu : u ≫ p = r) (V : Z.Opens) (T) : inU r (u ⁻¹ᵁ V) T ↔ inU p V ((smS u hu).G.obj T) := by
  subst hu
  exact (hs K Z Z Y p (𝟙 Z) u).2.2.2.2.1 V T

theorem inU_biInf (hs : SiteLaws) {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) {κ : Type} (V : κ → Z.Opens)
    (S : Finset κ) (T) : inU q (⨅ α ∈ S, V α) T ↔ ∀ α ∈ S, inU q (V α) T := by
  classical
  obtain ⟨-, -, htop, hinf, -, -⟩ := hs K Z Z Z q (𝟙 Z) (𝟙 Z)
  rw [← Finset.inf_eq_iInf]
  induction S using Finset.induction_on with
  | empty => simpa using htop T
  | insert a s ha ih =>
    rw [Finset.inf_insert, hinf, ih]
    simp

theorem capU_of_forall {C : Type 1} [Category.{0} C] {ι : Type} [DecidableEq ι] (U : ι → ObjectProperty C)
    (Q : ObjectProperty C) (S : Finset ι) (hS : S.Nonempty) (h : ∀ T, Q T ↔ ∀ α ∈ S, U α T) : capU U S = Q := by
  funext T
  refine propext ⟨fun hT => (h T).2 hT.2, fun hT => ?_⟩
  obtain ⟨α, hα⟩ := hS
  exact ⟨⟨α, (h T).1 hT α hα⟩, (h T).1 hT⟩

theorem capU_empty_eq {C : Type 1} [Category.{0} C] {ι : Type} [DecidableEq ι] (U : ι → ObjectProperty C) :
    (fun T => ∃ α, U α T) = capU U ∅ := by
  funext T
  exact propext ⟨fun h => ⟨h, fun α hα => absurd hα (Finset.notMem_empty α)⟩, fun h => h.1⟩

theorem res_self_bij {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C)
    (k : U ≤ U) (n : ℕ) : Function.Bijective ((resU F k).pull n) := by
  have h : ∀ x, (resU F k).pull n x = x := by
    intro x
    obtain ⟨a, ha, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj x
    rfl
  exact ⟨fun a b e => by rwa [h, h] at e, fun y => ⟨y, h y⟩⟩

theorem res_bij_of_eq {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    {U Q Q' : ObjectProperty C} (e : Q = Q') (h : Q ≤ U) (h' : Q' ≤ U) (n : ℕ)
    (hb : Function.Bijective ((resU F h).pull n)) : Function.Bijective ((resU F h').pull n) := by
  subst e
  exact hb

theorem kun_congr (E : XD K) {U₁ : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D}
    (e₂ : U₂ = U₂') (e₃ : U₃ = U₃') (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (h₁' : ∀ T, U₃' T → U₁ (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (h : E.Kun U₁ U₂ U₃ h₁ h₂) :
    E.Kun U₁ U₂' U₃' h₁' h₂' := by
  subst e₂ e₃
  exact h

theorem kun_right : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (d : ℕ), Nonempty (Coord q V d) → ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q V ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q V) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  intro hs hmv hcd hz hA hK K _ _ X X' P q q' _ _ p₁ p₂ hP V d cV h₁ h₂
  classical
  obtain ⟨U⟩ := (cov_ex q').1 inferInstance
  have hw : p₂ ≫ q' = p₁ ≫ q := hP.w.symm
  obtain ⟨hcosP, -, htopP, hinfP, -, -⟩ := hs K P P P (p₁ ≫ q) (𝟙 P) (𝟙 P)
  obtain ⟨hcos', -, htop', -, -, -⟩ := hs K X' X' X' q' (𝟙 X') (𝟙 X')
  have l₁ : ∀ (D : X'.Opens) T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ D) T → inU q V ((smS p₁ rfl).G.obj T) :=
    fun D T hT => (inU_pre hs p₁ rfl V T).1 ((hinfP _ _ T).1 hT).1
  have l₂ : ∀ (D : X'.Opens) T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ D) T → inU q' D ((smS p₂ hw).G.obj T) :=
    fun D T hT => (inU_pre hs p₂ hw D T).1 ((hinfP _ _ T).1 hT).2
  let E := hodgeXD q q' p₁ p₂ hw
  let Vv : U.ι → ObjectProperty E.C₂ := fun α => inU q' (U.U α)
  let Ww : U.ι → ObjectProperty E.D := fun α => inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ U.U α)
  have g₁ : ∀ (S : Finset U.ι) T, capU Ww S T → inU q V (E.L₁.obj T) := by
    rintro S T ⟨⟨α, hα⟩, -⟩
    exact l₁ _ T hα
  have g₂ : ∀ (S : Finset U.ι) T, capU Ww S T → capU Vv S (E.L₂.obj T) := by
    rintro S T ⟨⟨α, hα⟩, hS⟩
    exact ⟨⟨α, l₂ _ T hα⟩, fun β hβ => l₂ _ T (hS β hβ)⟩
  have eV : ∀ S : Finset U.ι, S.Nonempty → capU Vv S = inU q' (⨅ α ∈ S, U.U α) := fun S hS =>
    capU_of_forall _ _ S hS fun T => inU_biInf hs q' U.U S T
  have eW : ∀ S : Finset U.ι, S.Nonempty →
      capU Ww S = inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⨅ α ∈ S, U.U α) := fun S hS =>
    capU_of_forall _ _ S hS fun T => by
      obtain ⟨α₀, hα₀⟩ := hS
      rw [hinfP, inU_pre hs p₂ hw, inU_biInf hs q' U.U S]
      refine ⟨fun h α hα => (hinfP _ _ T).2 ⟨h.1, (inU_pre hs p₂ hw _ T).2 (h.2 α hα)⟩, fun h => ⟨((hinfP _ _ T).1 (h α₀ hα₀)).1, fun α hα => (inU_pre hs p₂ hw _ T).1 ((hinfP _ _ T).1 (h α hα)).2⟩⟩
  have hS : ∀ S : Finset U.ι, S.Nonempty → E.Kun (inU q V) (capU Vv S) (capU Ww S) (g₁ S) (g₂ S) := by
    intro S hne
    obtain ⟨α₀, hα₀⟩ := id hne
    obtain ⟨c', -⟩ := coord_res (U.c α₀) (iInf₂_le α₀ hα₀) (U.inter S hne)
    exact kun_congr E (eV S hne).symm (eW S hne).symm (l₁ _) (l₂ _) _ _
      (GlobalTheory.T.kuenneth_product_local_coords hs hA hK K X X' P q q' p₁ p₂ hP V _ d _ cV ⟨c'⟩ (l₁ _) (l₂ _))
  have hglue := _root_.GlobalTheory.CompanionTheory.KunGlue.glue_r hmv hcd E (inU q V) Vv Ww (fun α => hcos' _) (fun α => hcosP _) g₁ g₂ hS
  have k₂ : capU Vv ∅ ≤ inU q' ⊤ := fun T _ => htop' T
  have k₃ : capU Ww ∅ ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨⟨α, hα⟩, -⟩
    exact (hinfP _ _ T).2 ⟨((hinfP _ _ T).1 hα).1, (inU_pre hs p₂ hw _ T).2 (htop' _)⟩
  have sup₃ : (⨆ α, p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ U.U α) = p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ ⊤ := by
    rw [← inf_iSup_eq, ← U.cover]
    congr 1
    ext x
    simp [TopologicalSpace.Opens.mem_iSup]
  refine (GlobalTheory.T.kuenneth_of_restrict_bijective E h₁ h₂ (g₁ ∅) (g₂ ∅) (le_refl _) k₂ k₃ ?_ ?_ ?_).2 hglue
  · exact fun a n => res_self_bij _ _ _ n
  · intro a n
    exact res_bij_of_eq (G q' a) (capU_empty_eq Vv) (fun _ _ => htop' _) k₂ n
      (hz K X' q' U.ι ⊤ U.U U.cover _ a n)
  · intro a n
    refine res_bij_of_eq (G (p₁ ≫ q) a) (capU_empty_eq Ww) (fun T hT => k₃ T ((capU_empty_eq Ww ▸ hT : capU Ww ∅ T))) k₃ n
      (hz K P (p₁ ≫ q) U.ι _ (fun α => p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ U.U α) sup₃ _ a n)

end GlobalTheory.CompanionTheory.KunGlue.Right
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitNodeEmbedding
section
noncomputable section

open NumberField
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.TreeNode

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mulChi_absC_mulChi (n : ℕ) (z z' : ℂ) (φ : Sm E n) :
    mulChi n (Model.absC E z) (mulChi n (Model.absC E z') φ) = mulChi n (Model.absC E (z' + z)) φ := by
  refine Subtype.ext (funext fun g => ?_)
  rw [mulChi_apply, mulChi_apply, mulChi_apply, ExponentTwist.chiDet_absC_val, ExponentTwist.chiDet_absC_val,
    ExponentTwist.chiDet_absC_val, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem tw_tw {n : ℕ} (V : Submodule ℂ (Sm E n)) (a b : ℂ) : tw (tw V a) b = tw V (a + b) := by
  ext ψ
  constructor
  · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    exact ⟨φ, hφ, (mulChi_absC_mulChi n b a φ).symm⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨_, ⟨φ, hφ, rfl⟩, mulChi_absC_mulChi n b a φ⟩

theorem map_mem_finVec {n : ℕ} {V : Submodule ℂ (Sm E n)} (f : Sm E n →ₗ[ℂ] Sm E n)
    (heq : ∀ o, ∀ φ ∈ V, f (act o φ) = act o (f φ)) {φ : Sm E n} (hφ : φ ∈ V)
    (hfin : φ ∈ finVec (cptRep E n)) : f φ ∈ finVec (cptRep E n) := by
  have h : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E n k φ)) := hfin
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E n k (f φ)))
  refine Submodule.finiteDimensional_of_le
    (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E n k φ)).map f) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, heq (.cpt k) φ hφ⟩

theorem nodeEmb : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.NodeEmb := by
  rintro E _ _ _ r s V V₁ V₂ z₁ z₂ hV ⟨f, hf, hinj, heq⟩
  refine ⟨f, fun φ hφ => Submodule.subset_span ⟨?_, ?_⟩, hinj, heq⟩
  · have e₁ : tw (tw V₁ (z₁ - (s : ℂ) / 2)) ((s : ℂ) / 2) = tw V₁ z₁ := by
      rw [tw_tw, sub_add_cancel]
    have e₂ : tw (tw V₂ (z₂ + (r : ℂ) / 2)) (-(r : ℂ) / 2) = tw V₂ z₂ := by
      rw [tw_tw, neg_div, add_neg_cancel_right]
    change MemInd2 (tw (tw V₁ (z₁ - (s : ℂ) / 2)) ((s : ℂ) / 2)) (tw (tw V₂ (z₂ + (r : ℂ) / 2)) (-(r : ℂ) / 2)) (f φ)
    rw [e₁, e₂]
    exact hf φ hφ
  · exact map_mem_finVec f heq hφ (hV.aut φ hφ).kfin

end GlobalTheory.CompanionTheory.TreeNode

end
end

