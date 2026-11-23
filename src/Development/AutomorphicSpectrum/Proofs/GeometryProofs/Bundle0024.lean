module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicElementHomogRelationStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_element_homog_relation : ∀ (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (i : Ω₀ →+* Ω) (α : Ω), Birational y₀ → (letI := i.toAlgebra; IsAlgebraic Ω₀ α) → ∃ (n : ℕ) (c : ℕ → MRing J₀) (a : K₀ → ℕ) (G : MRing J₀) (b : K₀ → ℕ), (∀ j, IsMultiHomog (c j) a) ∧ IsMultiHomog G b ∧ G ∉ mCoordIdeal y₀ ∧ (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * α ^ j = 0) ∧ ∀ w ∈ mcPts (mCoordIdeal y₀), eval w (map (Int.castRingHom ℂ) G) ≠ 0 → ∀ τ : ℂ, ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ j = 0 → ∑ j ∈ Finset.range (n + 1), (j : ℂ) * eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ (j - 1) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AlgPoly.algebraic_form_poly | exact GlobalTheory.CompanionTheory.Ar.AlgPoly.algebraic_form_poly | (intros; apply GlobalTheory.CompanionTheory.Ar.AlgPoly.algebraic_form_poly <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEval
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.ValEmb

theorem valAt_pull {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}}
    (j : X ⟶ Spec (CommRingCat.of A)) (x : Spec (CommRingCat.of B) ⟶ X) (ρ : A →+* B)
    (h : x ≫ j = Spec.map (CommRingCat.ofHom ρ)) (f : A) :
    valAt x ⊤ le_top (j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom f)) = ρ f := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop ≫ x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      = CommRingCat.ofHom ρ := by
    have : j.appTop ≫ x.appTop = (Spec.map (CommRingCat.ofHom ρ)).appTop := by
      rw [← h, Scheme.Hom.comp_appTop]
    rw [reassoc_of% this, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  have h2 := congrArg (fun φ => φ.hom f) h1
  have hle : x.appLE ⊤ ⊤ le_top = x.appTop := by
    simp only [Scheme.Hom.appLE]
    exact Category.comp_id _
  simp only [valAt]
  rw [hle]
  simpa using h2

theorem valAt_sub {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) : valAt x U h (a - b) = valAt x U h a - valAt x U h b := by
  simp [valAt]

theorem val_emb : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → ∀ (f : Γ.btOrder ⊤) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (f : T → R) → ∀ (B : Type) [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (ρ : (Γ.btOrder ⊤) →+* B), y ≫ j = Spec.map (CommRingCat.ofHom ρ) → valAt y ⊤ le_top s = ρ f := by
  intro R _ _ T _ _ Γ j hj f s hs B _ y ρ hy
  have hz : s - j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ.btOrder ⊤))).inv.hom f) = 0 := by
    refine _root_.GlobalTheory.CompanionTheory.Ar.BT.section_eq_zero_of_val_generic R T Γ ⊤ _ fun t h => ?_
    rw [valAt_sub, hs t, valAt_pull j (Γ.pt t).left _ (hj.pt t) f]
    simp
  rw [sub_eq_zero.mp hz]
  exact valAt_pull j y ρ hy f

end GlobalTheory.CompanionTheory.Ar.BT.ValEmb
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleLatticeGenerators
section
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem dotDual_overlap : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (L : ι → AddSubgroup (Fin r → Ω)),
    (∀ c, ∀ a ∈ chartRing O x c, ∀ e ∈ L c, a • e ∈ L c) →
    (∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ L i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ L j) →
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ L c) ∧
      ∀ e ∈ L c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ dotDual (chartRing O x i) (L i),
      ∃ m : ℕ, (x i / x j) ^ m • e ∈ dotDual (chartRing O x j) (L j) :=
  PositivityTheory.Xgn.hodge_dual_lattice_overlap

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleLocalGeneration
section
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem chartBundle_dotDual_localFrame : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)),
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing O x i) ∧ (∀ l, c l ∈ chartRing O x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, ∃ b : Fin r → Fin r → Ω, LinearIndependent Ω b ∧
        Submodule.span Ω (Set.range b) = ⊤ ∧ ∀ e : Fin r → Ω,
          ((∃ n : ℕ, f l ^ n • e ∈ dotDual (chartRing O x i) (B.lat i)) ↔
            ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing O x i) ∧ e = ∑ q, a q • b q) :=
  PositivityTheory.Xgn.hodge_dual_frame_exists

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

def GenIx {S : Type} (r : S → ℕ) : Type := Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1}

abbrev GenField (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) : Type :=
  FractionRing (MvPolynomial (GenIx r) Ω)

def genU (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) :
    Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := fun l k =>
  if h : k < l then algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩)
  else if l = k then 1 else 0

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {S : Type} {r : S → ℕ}

def genB (c : ∀ s, Fin (r s) → E) (s : S) (k : Fin (r s)) : TensorProduct Ω (GenField Ω r) E :=
  ∑ l, genU Ω r s l k • TensorProduct.mk Ω (GenField Ω r) E 1 (c s l)

def flagMat {n : S → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S) :
    Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) :=
  Matrix.of (fun j l => algebraMap Ω (GenField Ω r) (φ s j (c s l))) * genU Ω r s

def FlagIx (κ : Type) {S : Type} (n : S → ℕ) (r : S → ℕ) : Type :=
  κ × ((q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1))

def flagCoord [Fintype S] (κ : Type) (x : κ → Ω) {n : S → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (c : ∀ s, Fin (r s) → E) : FlagIx κ n r → GenField Ω r := fun cJ =>
  algebraMap Ω (GenField Ω r) (x cJ.1) *
    ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (cJ.2 q) (Fin.castLE q.2.2)).det

def IsTwistGen {X : Scheme.{0}} (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type} (x : κ → Ω) (L : Lat ξ E) (m : ℕ)
    {n : ℕ} (φ : Fin n → Module.Dual Ω E) : Prop :=
  (∀ j (p : Cpt ξ) c, InChart ξ x c p → ∀ e ∈ L p, φ j e / x c ^ m ∈ regAt ξ p) ∧
  ∀ (p : Cpt ξ) c, InChart ξ x c p → ∀ w : Module.Dual Ω E, (∀ e ∈ L p, w e ∈ regAt ξ p) →
    ∃ g : Fin n → Ω, (∀ j, g j ∈ regAt ξ p) ∧ ∀ e ∈ L p, w e = ∑ j, g j * (φ j e / x c ^ m)

theorem coordTie_comp_equiv {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {o : Type}
    [CommRing o] [Algebra o Ω] {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' ≃ κ) :
    CoordTie o ξ (x ∘ e) := by
  have hch : ∀ c p, InChart ξ (x ∘ e) c p ↔ InChart ξ x (e c) p := by
    intro c p
    simp only [InChart, Function.comp]
    exact and_congr Iff.rfl ⟨fun h c' => by simpa using h (e.symm c'), fun h c' => h (e c')⟩
  have hr : ∀ c, Set.range (fun j => (x ∘ e) j / (x ∘ e) c) = Set.range (fun j => x j / x (e c)) := by
    intro c
    ext a
    exact ⟨fun ⟨j, hj⟩ => ⟨e j, hj⟩, fun ⟨j, hj⟩ => ⟨e.symm j, by simpa using hj⟩⟩
  refine ⟨h.gen, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := h.cover p
    exact ⟨e.symm c, (hch _ p).2 (by simpa using hc)⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) hc
    exact ⟨U, hU, fun q => by rw [hq q]; exact exists_congr fun h' => (hch c _).symm⟩
  · rw [hr c, h.ring (e c) hc a]
    exact forall_congr' fun p => imp_congr (hch c p).symm Iff.rfl
end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExact
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

namespace FlagGr

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}

theorem coeff_eq_zero {b : Fin r → E} (hb : LinearIndependent Ω b) {s : ℕ} (c : Fin r → Ω)
    (h : ∑ k, c k • b k ∈ flagStep Ω b s) (k : Fin r) (hk : ¬ (k : ℕ) < s) : c k = 0 := by
  obtain ⟨l, hl, hl'⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 h
  have h1 : ∑ k, (l k) • b k = ∑ k, c k • b k := by
    rw [← hl', Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  have h2 := (Fintype.linearIndependent_iff.1 hb) (fun k => l k - c k)
    (by simp [sub_smul, Finset.sum_sub_distrib, h1]) k
  have h3 : l k = 0 := (Finsupp.mem_supported' Ω l).1 hl k hk
  simpa [h3] using h2

theorem mem_step (b : Fin r → E) {s : ℕ} {k : Fin r} (hk : (k : ℕ) < s) : b k ∈ flagStep Ω b s :=
  Submodule.subset_span ⟨k, hk, rfl⟩

theorem step_mono (b : Fin r → E) {s s' : ℕ} (h : s ≤ s') : flagStep Ω b s ≤ flagStep Ω b s' :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

theorem eq_zero_of_smul_mem {b : Fin r → E} (hb : LinearIndependent Ω b) (i : Fin r) {t : Ω}
    (h : t • b i ∈ flagStep Ω b i) : t = 0 := by
  have := coeff_eq_zero hb (s := i) (Pi.single i t) (by simpa [Pi.single_apply] using h) i (lt_irrefl _)
  simpa using this

theorem step_top (b : Fin r → E) : flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold flagStep
  congr 1
  ext x
  simp

theorem range_castLE (b : Fin r → E) {s : ℕ} (hs : s ≤ r) :
    Set.range (b ∘ Fin.castLE hs) = b '' {k | (k : ℕ) < s} := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨Fin.castLE hs k, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem exists_diag (b : Fin r → E) (i : Fin r) {e : E} (he : e ∈ flagStep Ω b (i + 1)) :
    ∃ t : Ω, e - t • b i ∈ flagStep Ω b i := by
  have hs : b '' {k : Fin r | (k : ℕ) < i + 1} = insert (b i) (b '' {k : Fin r | (k : ℕ) < i}) := by
    rw [← Set.image_insert_eq]
    congr 1
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  unfold flagStep at he
  rw [hs, Submodule.mem_span_insert] at he
  obtain ⟨t, z, hz, rfl⟩ := he
  exact ⟨t, by simpa [flagStep] using hz⟩

theorem span_inf_step (R : Subring Ω) {b : Fin r → E} (hb : LinearIndependent Ω b) (s : ℕ) :
    Submodule.span R (Set.range b) ⊓ (flagStep Ω b s).restrictScalars R =
      Submodule.span R (b '' {k | (k : ℕ) < s}) := by
  apply le_antisymm
  · rintro e ⟨he, he'⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 he
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : (k : ℕ) < s
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · have h0 : (c k : Ω) = 0 := coeff_eq_zero hb (fun k => (c k : Ω)) he' k hk
      have : c k = 0 := Subtype.ext h0
      simp [this]
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨Submodule.subset_span ⟨k, rfl⟩, mem_step b hk⟩

theorem gr_eq (R : Subring Ω) {b b₀ : Fin r → E} (hb : LinearIndependent Ω b) (hb₀ : LinearIndependent Ω b₀)
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) {t : Ω} (ht : b i - t • b₀ i ∈ flagStep Ω b₀ i) :
    Submodule.span R {u : Ω | ∃ e ∈ Submodule.span R (Set.range b), e - u • b₀ i ∈ flagStep Ω b₀ i} =
      Submodule.span R {t} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro u ⟨e, he, hu⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 he
    have h1 : ∑ k, c k • b k ∈ flagStep Ω b (i + 1) := by
      rw [hF]
      have := Submodule.add_mem _ (step_mono b₀ (Nat.le_succ _) hu)
        (Submodule.smul_mem _ u (mem_step b₀ (Nat.lt_succ_self (i : ℕ))))
      simpa using this
    have h2 : ∑ k, c k • b k - (c i : Ω) • b i ∈ flagStep Ω b₀ i := by
      rw [← hF, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      have : ∑ k ∈ Finset.univ.erase i, c k • b k ∈ flagStep Ω b i := by
        refine Submodule.sum_mem _ fun k hk => ?_
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        change (c k : Ω) • b k ∈ _
        by_cases hk' : (k : ℕ) < i
        · exact Submodule.smul_mem _ _ (mem_step b hk')
        · have h0 : (c k : Ω) = 0 := coeff_eq_zero hb (fun k => (c k : Ω)) h1 k (by
            have : (k : ℕ) ≠ i := fun h => hki (Fin.ext h)
            omega)
          simp [h0]
      have e2 : c i • b i = (c i : Ω) • b i := rfl
      rw [e2, add_sub_cancel_right]
      exact this
    have h3 : ((c i : Ω) * t - u) • b₀ i ∈ flagStep Ω b₀ i := by
      have := Submodule.sub_mem _ (Submodule.sub_mem _ hu h2) (Submodule.smul_mem _ (c i : Ω) ht)
      convert this using 1
      rw [sub_smul, smul_sub, mul_smul]
      abel
    have h4 := eq_zero_of_smul_mem hb₀ i h3
    exact Submodule.mem_span_singleton.2 ⟨c i, sub_eq_zero.1 h4⟩
  · refine Submodule.span_mono ?_
    rintro _ rfl
    exact ⟨b i, Submodule.subset_span ⟨i, rfl⟩, ht⟩

end FlagGr


open FlagGr in
theorem Lat.IsFlagVBOn.isVBOn_gr_inter : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (b₀ : Fin r → E), LinearIndependent Ω b₀ → L.IsFlagVBOn T b₀ → L.IsVBOn T r (Submodule.span Ω (Set.range b₀)) ∧ (∀ i, (L.gr b₀ i).IsVBOn T 1 ⊤) ∧ ∀ s : ℕ, s ≤ r → (L.inter (flagStep Ω b₀ s)).IsVBOn T s (flagStep Ω b₀ s) := by
  intro X Ω _ ξ E _ _ L T r b₀ hb₀ hL
  refine ⟨fun p hp => ?_, fun i p hp => ?_, fun s hs p hp => ?_⟩
  · obtain ⟨U, hU, b, hF, hb⟩ := hL p hp
    exact ⟨U, hU, b, by rw [← step_top, hF, step_top], hb⟩
  · obtain ⟨U, hU, b, hF, hb⟩ := hL p hp
    have hli := (hb p hp hU).1
    obtain ⟨t, ht⟩ := exists_diag b₀ i (e := b i) (hF _ ▸ mem_step b (Nat.lt_succ_self (i : ℕ)))
    have ht0 : t ≠ 0 := by
      rintro rfl
      have : (1 : Ω) • b i ∈ flagStep Ω b i := by simpa [hF] using ht
      exact one_ne_zero (eq_zero_of_smul_mem hli i this)
    have hr : Set.range (fun _ : Fin 1 => t) = {t} := Set.range_const
    refine ⟨U, hU, fun _ => t, ?_, fun q hq hqU => ⟨?_, ?_⟩⟩
    · rw [hr, eq_top_iff]
      intro x _
      exact Submodule.mem_span_singleton.2 ⟨x / t, by simp [ht0]⟩
    · exact linearIndependent_unique_iff.2 ht0
    · rw [hr]
      unfold Lat.gr
      rw [(hb q hq hqU).2]
      exact gr_eq _ hli hb₀ hF i ht
  · obtain ⟨U, hU, b, hF, hb⟩ := hL p hp
    have hli := (hb p hp hU).1
    refine ⟨U, hU, b ∘ Fin.castLE hs, ?_, fun q hq hqU => ⟨hli.comp _ (Fin.castLE_injective hs), ?_⟩⟩
    · rw [range_castLE, ← hF]
      rfl
    · unfold Lat.inter
      rw [(hb q hq hqU).2, range_castLE, ← hF]
      exact span_inf_step _ hli s

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIntegralAdeleLimitCompatibleIntSystem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar

theorem eigSp_comp_ringEquiv : ∀ (R E O : Type) [CommRing R] [AddCommGroup E] [Module R E] [CommRing O] (ρ : O →+* Module.End R E) (s : O ≃+* O) (τ : O →+* R), eigSp (ρ.comp s.toRingHom) (τ.comp s.toRingHom) = eigSp ρ τ := by
  intro R E O _ _ _ _ ρ s τ
  unfold eigSp
  exact s.surjective.iInf_comp (fun b => LinearMap.ker (ρ b - τ b • LinearMap.id))

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagCoefficientRatioIntegral
section
open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem leadCoef_ratio_mem (Ω : Type) [Field Ω] (Li : Type) [AddCommGroup Li] [Module Ω Li] (W : Subring Ω) (r : ℕ)
    (b₀ b b' : Fin r → Li) (N : Ω) (k : Fin r) (t t' : Ω) (hb : LinearIndependent Ω b)
    (hbf : ∀ j, flagStep Ω b j = flagStep Ω b₀ j) (_hbf' : ∀ j, flagStep Ω b' j = flagStep Ω b₀ j)
    (hN : ∀ j, N • b' j ∈ Submodule.span W (Set.range b))
    (ht : b k - t • b₀ k ∈ flagStep Ω b₀ k) (ht' : b' k - t' • b₀ k ∈ flagStep Ω b₀ k) :
    N * (t' / t) ∈ W := by
  by_cases ht0 : t = 0
  · rw [ht0, div_zero, mul_zero]
    exact W.zero_mem
  obtain ⟨u, hu_def⟩ : ∃ u : Ω, u = t' / t := ⟨_, rfl⟩
  rw [← hu_def]
  have hu : u * t = t' := by rw [hu_def, div_mul_cancel₀ t' ht0]
  have hF : N • b' k - (N * u) • b k ∈ flagStep Ω b k := by
    rw [hbf]
    have h1 := Submodule.sub_mem _ (Submodule.smul_mem _ N ht') (Submodule.smul_mem _ (N * u) ht)
    rw [← hu] at h1
    convert h1 using 1
    module
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun W).mp (hN k)
  rw [← hw] at hF
  have hF' : (∑ i, w i • b i) - (N * u) • b k ∈ Submodule.span Ω (b '' {j : Fin r | (j : ℕ) < k}) := hF
  obtain ⟨l, hl, hlc⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).mp hF'
  have hsum : Finsupp.linearCombination Ω b
      (Finsupp.equivFunOnFinite.symm fun i => (w i : Ω) - if i = k then N * u else 0) =
      (∑ i, w i • b i) - (N * u) • b k := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ (fun i a => a • b i) (fun i => zero_smul Ω _)]
    simp only [Finsupp.coe_equivFunOnFinite_symm, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Subring.smul_def]
  have h0 : Finsupp.linearCombination Ω b
      ((Finsupp.equivFunOnFinite.symm fun i => (w i : Ω) - if i = k then N * u else 0) - l) = 0 := by
    rw [map_sub, hsum, hlc, sub_self]
  have hl0 := sub_eq_zero.mp (linearIndependent_iff.mp hb _ h0)
  have hk := DFunLike.congr_fun hl0 k
  simp only [Finsupp.coe_equivFunOnFinite_symm, ↓reduceIte] at hk
  have hlk : l k = 0 := (Finsupp.mem_supported' Ω l).mp hl k (by simp)
  rw [hlk, sub_eq_zero] at hk
  rw [← hk]
  exact (w k).2

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTrdegFormula
section
open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagTrdeg

open scoped IntermediateField.algebraAdjoinAdjoin

theorem card_below_diagonal (n : ℕ) :
    Fintype.card {lk : Fin n × Fin n // lk.2 < lk.1} = n * (n - 1) / 2 := by
  rw [show Fintype.card {lk : Fin n × Fin n // lk.2 < lk.1} = Fintype.card (Σ a : Fin n, {b : Fin n // b < a}) from
    Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b : Fin n => b < a), Fintype.card_sigma]
  have h : ∀ a : Fin n, Fintype.card {b : Fin n // b < a} = a := by
    intro a
    rw [Fintype.card_subtype]
    have e : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by
      ext b
      simp
    rw [e, Fin.card_Iio]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

theorem isTranscendenceBasis_of_adjoin {k K ι : Type} [Field k] [Field K] [Algebra k K] {x : ι → K}
    (hx : AlgebraicIndependent k x)
    (h : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K) :
    IsTranscendenceBasis k x := by
  rw [hx.isTranscendenceBasis_iff_isAlgebraic]
  exact (IsFractionRing.comap_isAlgebraic_iff (A := ↥(Algebra.adjoin k (Set.range x)))
    (K := ↥(IntermediateField.adjoin k (Set.range x))) (C := K)).2 h

theorem trdeg_of_isGenericFlag (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E : Type) [AddCommGroup E]
    [Module Ω₀ E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (j : E →+ E') (S : Type) [Fintype S]
    (r : S → ℕ) (V : S → Submodule Ω₀ E) (b₀ : ∀ σ, Fin (r σ) → E') (d : ℕ)
    (hg : IsGenericFlag (Ω' := Ω) j V b₀ d) :
    Algebra.trdeg Ω₀ Ω = ((∑ σ, r σ * (r σ - 1) / 2 : ℕ) : Cardinal) := by
  obtain ⟨c, u, -, -, -, -, hdiag, hup, -, hind, hd, hfr⟩ := hg
  have heq : IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨σ, l, k⟩, rfl⟩
      rcases lt_trichotomy k l with hkl | hkl | hkl
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, ⟨(l, k), hkl⟩⟩, rfl⟩
      · subst hkl
        simp only [hdiag]
        exact one_mem _
      · simp only [hup σ l k hkl]
        exact zero_mem _
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨σ, ⟨⟨l, k⟩, hkl⟩⟩, rfl⟩
      exact IntermediateField.subset_adjoin _ _ ⟨⟨σ, (l, k)⟩, rfl⟩
  haveI : Module.Finite (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact hd)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin Ω₀
      (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) Ω :=
    Algebra.IsAlgebraic.of_finite _ _
  rw [heq] at halg
  have hb := isTranscendenceBasis_of_adjoin hind halg
  rw [← hb.cardinalMk_eq_trdeg, Cardinal.mk_fintype, Fintype.card_sigma]
  simp only [card_below_diagonal]

end GlobalTheory.CompanionTheory.Ar.FlagTrdeg
end

