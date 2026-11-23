module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsTwoPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFamiliesThetaSymmetricMinMemberCompare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.PrimCmp

theorem esymm_map_hom {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') (M : Multiset R) (j : ℕ) :
    (M.map i).esymm j = i (M.esymm j) := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s _ => ?_)
  simp only [Function.comp, map_multiset_prod]

theorem symTup_map {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun b => i (c b)) j := by
  unfold symTup
  rw [map_pow]
  congr 1
  have hm : Finset.univ.val.map (fun b => i (c b)) = (Finset.univ.val.map c).map i := by
    rw [Multiset.map_map]; rfl
  rw [hm, esymm_map_hom]

theorem esymm_map_mul {R : Type} [CommRing R] {A : Type} (t : R) (M : Multiset A) (f : A → R) (j : ℕ) :
    (M.map fun b => t * f b).esymm j = t ^ j * (M.map f).esymm j := by
  have : (M.map fun b => t * f b) = (M.map f).map (fun x => t * x) := by rw [Multiset.map_map]; rfl
  rw [this]
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s hs => ?_)
  have hc := (Multiset.mem_powersetCard.1 hs).2
  simp only [Function.comp]
  rw [Multiset.prod_map_mul]
  simp [hc]

theorem symTup_mul {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (t : R) (j : Fin N) :
    symTup (fun b => t * c b) j = t ^ N.factorial * symTup c j := by
  unfold symTup
  have h := esymm_map_mul t (Finset.univ.val) c ((j : ℕ) + 1)
  rw [h, mul_pow, ← pow_mul, Nat.mul_div_cancel' (Nat.dvd_factorial (Nat.succ_pos _) j.2)]

theorem mem_of_isIntegralElem {V K : Type} [CommRing V] [Field K] (i : V →+* K) (W : ValuationSubring K)
    (hW : ∀ v, i v ∈ W) {x : K} (hx : i.IsIntegralElem x) : x ∈ W := by
  obtain ⟨p, hm, hp⟩ := hx
  let φ : V →+* W := i.codRestrict W.toSubring hW
  have hφ : (algebraMap W K).comp φ = i := by ext v; rfl
  have hint : IsIntegral W x := ⟨p.map φ, hm.map φ, by rw [Polynomial.eval₂_map, hφ]; exact hp⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact y.2

theorem mem_of_pow_mem {K : Type} [Field K] (W : ValuationSubring K) {w : K} {k : ℕ} (hk : 1 ≤ k)
    (h : w ^ k ∈ W) : w ∈ W := by
  rw [← W.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff (by omega)).1 h

theorem mem_range_of_forall {V K : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field K]
    (io : FractionRing V →+* K) (z : FractionRing V)
    (h : ∀ W : ValuationSubring K, (∀ v, io (algebraMap V (FractionRing V) v) ∈ W) → io z ∈ W) :
    z ∈ Set.range (algebraMap V (FractionRing V)) := by
  letI : Algebra V K := (io.comp (algebraMap V (FractionRing V))).toAlgebra
  have hic : IsIntegrallyClosedIn (integralClosure V K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure V K) K)
  have h1 : io z ∈ (integralClosure V K).toSubring := by
    by_contra hn
    obtain ⟨W, hW, hzW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hn
    exact hzW (h W (fun v => hW ((integralClosure V K).algebraMap_mem v)))
  let f : FractionRing V →ₐ[V] K := { io with commutes' := fun _ => rfl }
  have h2 : IsIntegral V z := (isIntegral_algHom_iff f (f : FractionRing V →+* K).injective).1 h1
  exact IsIntegrallyClosed.isIntegral_iff.1 h2

end GlobalTheory.UMin.PrimCmp

namespace GlobalTheory.UMin.PrimCmp

theorem key {V K : Type} [CommRing V] [IsDomain V] [Field K] (io : FractionRing V →+* K) (N : ℕ) (c : Fin N → K) (a : K)
    (ha : a ≠ 0) (hP : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a)) (e : Fin N → FractionRing V)
    (he : ∀ j, io (e j) = symTup c j) (j₀ : Fin N) (he0 : e j₀ ≠ 0)
    (hq : ∀ j, e j / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) (W : ValuationSubring K)
    (hW : ∀ v, io (algebraMap V (FractionRing V) v) ∈ W) :
    io (e j₀) / a ^ N.factorial ∈ W ∧ (io (e j₀) / a ^ N.factorial)⁻¹ ∈ W := by
  have hcW : ∀ b, c b / a ∈ W := fun b => mem_of_isIntegralElem _ W hW (hP.1 b)
  obtain ⟨b₀, hb0, hb0i⟩ := hP.2
  have hb0W : (c b₀ / a)⁻¹ ∈ W := mem_of_isIntegralElem _ W hW hb0i
  let y : Fin N → W := fun b => ⟨c b / a, hcW b⟩
  have hu : IsUnit (y b₀) := (Units.mkOfMulEqOne (y b₀) ⟨_, hb0W⟩ (Subtype.ext (show c b₀ / a * (c b₀ / a)⁻¹ = 1 from mul_inv_cancel₀ hb0))).isUnit
  let z : Fin N → W := fun b => y b * ↑hu.unit⁻¹
  have hz : z b₀ = 1 := by simp [z]
  obtain ⟨k, hk1, hkN, hku⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one W (Fin N) z b₀ hz
  have hyz : ∀ b, y b = y b₀ * z b := by
    intro b; simp only [z]; rw [mul_left_comm, IsUnit.mul_val_inv, _root_.mul_one]
  have hesy : IsUnit ((Finset.univ.val.map y).esymm k) := by
    have hm : Finset.univ.val.map y = Finset.univ.val.map (fun b => y b₀ * z b) :=
      Multiset.map_congr rfl fun b _ => hyz b
    rw [hm, esymm_map_mul]
    exact (hu.pow k).mul hku
  have hkN' : k ≤ N := by simpa using hkN
  let j₁ : Fin N := ⟨k - 1, by omega⟩
  have hsy : IsUnit (symTup y j₁) := by
    unfold symTup
    have : (j₁ : ℕ) + 1 = k := by simp only [j₁]; omega
    rw [this]
    exact hesy.pow _
  have hcoe : ∀ j, ((symTup y j : W) : K) = io (e j) / a ^ N.factorial := by
    intro j
    have h1 := symTup_map W.subtype y j
    rw [ValuationSubring.coe_subtype] at h1
    rw [h1]
    have h2 : (fun b => ((y b : W) : K)) = fun b => a⁻¹ * c b := by
      funext b; simp [y, div_eq_inv_mul]
    rw [h2, symTup_mul, he, inv_pow, inv_mul_eq_div]
  have ht : io (e j₀) / a ^ N.factorial ∈ W := hcoe j₀ ▸ (symTup y j₀).2
  obtain ⟨v, hv⟩ := hq j₁
  have hr : io (e j₁ / e j₀) ∈ W := by rw [← hv]; exact hW v
  have hio0 : io (e j₀) ≠ 0 := (map_ne_zero io).2 he0
  have hsplit : symTup y j₁ = ⟨_, hr⟩ * ⟨_, ht⟩ := by
    apply Subtype.ext
    rw [hcoe]
    show _ = io (e j₁ / e j₀) * (io (e j₀) / a ^ N.factorial)
    rw [map_div₀]
    field_simp
  rw [hsplit] at hsy
  have htu := isUnit_of_mul_isUnit_right hsy
  refine ⟨ht, ?_⟩
  have h3 : ((↑htu.unit⁻¹ : W) : K) * (io (e j₀) / a ^ N.factorial) = 1 := by
    have := congrArg Subtype.val (IsUnit.val_inv_mul htu)
    rw [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    exact this
  rw [← eq_inv_of_mul_eq_one_left h3]
  exact (↑htu.unit⁻¹ : W).2

end GlobalTheory.UMin.PrimCmp

theorem GlobalTheory.UMin.prim_symTup_cmp : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field K] (io : FractionRing V →+* K) (N N' k : ℕ) (J : Type) (c : Fin N → K) (c' : Fin N' → K) (a : K) (e : Fin N → FractionRing V) (th : J → FractionRing V), a ≠ 0 → 1 ≤ k → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a) → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a) → (∀ j, io (e j) = symTup c j) → (∀ x, ∃ b, c' x ^ k = io (th b) ^ k) → (∀ b, ∃ x, c' x ^ k = io (th b) ^ k) → ∀ j₀, e j₀ ≠ 0 → (∀ j, e j / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) → (∀ b, th b ^ N.factorial / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) ∧ ∃ b, th b ≠ 0 ∧ e j₀ / th b ^ N.factorial ∈ Set.range (algebraMap V (FractionRing V)) := by
  intro V K _ _ _ _ io N N' k J c c' a e th ha hk hP hP' he hth1 hth2 j₀ he0 hq
  refine ⟨fun b => ?_, ?_⟩
  · apply GlobalTheory.UMin.PrimCmp.mem_range_of_forall io
    intro W hW
    obtain ⟨-, hti⟩ := GlobalTheory.UMin.PrimCmp.key io N c a ha hP e he j₀ he0 hq W hW
    obtain ⟨x, hx⟩ := hth2 b
    have hw : io (th b) / a ∈ W := by
      refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
      rw [div_pow, ← hx, ← div_pow]
      exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW (hP'.1 x)) k
    have hio0 : io (e j₀) ≠ 0 := (map_ne_zero io).2 he0
    have heq : io (th b ^ N.factorial / e j₀) = (io (th b) / a) ^ N.factorial * (io (e j₀) / a ^ N.factorial)⁻¹ := by
      rw [map_div₀, map_pow, div_pow, inv_div]
      field_simp
    rw [heq]
    exact mul_mem (pow_mem hw _) hti
  · obtain ⟨x₀, hx0, hx0i⟩ := hP'.2
    obtain ⟨b₁, hb1⟩ := hth1 x₀
    have hk0 : k ≠ 0 := by omega
    have hth0 : io (th b₁) ≠ 0 := by
      intro h0
      apply hx0
      have h2 : c' x₀ ^ k = 0 := by rw [hb1, h0, zero_pow hk0]
      simp [pow_eq_zero_iff hk0 |>.1 h2]
    refine ⟨b₁, fun h => hth0 (by rw [h, map_zero]), ?_⟩
    apply GlobalTheory.UMin.PrimCmp.mem_range_of_forall io
    intro W hW
    obtain ⟨ht, -⟩ := GlobalTheory.UMin.PrimCmp.key io N c a ha hP e he j₀ he0 hq W hW
    have hwi : (io (th b₁) / a)⁻¹ ∈ W := by
      refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
      rw [inv_pow, div_pow, ← hb1, ← div_pow, ← inv_pow]
      exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW hx0i) k
    have heq : io (e j₀ / th b₁ ^ N.factorial) = (io (e j₀) / a ^ N.factorial) * ((io (th b₁) / a)⁻¹) ^ N.factorial := by
      rw [map_div₀, map_pow, inv_div, div_pow]
      field_simp
    rw [heq]
    exact mul_mem ht (pow_mem hwi _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin

theorem isGenSec_of_univBasis {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {K K' : Type} [CommRing K]
    [CommRing K'] {x : Sp K ⟶ S} {e : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))} (he : UnivBasis G L x e)
    (i : K →+* K') {x' : Sp K' ⟶ S} (h : spMap i ≫ x = x') :
    IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) e) :=
  (isGenSec_iff _).2 fun s => by
    obtain ⟨c, hc, -⟩ := he K' i x' h s
    exact ⟨c, hc⟩

theorem spMap_id (K : Type) [CommRing K] : spMap (RingHom.id K) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

theorem gen_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (g : ℕ) (K : Type)
    [Field K] (x : Sp K ⟶ S), PolFib G L g x → (∃ θ : SecAt G L x, IsGenSec G L _ θ) ∧
    ∀ θ : SecAt G L x, IsGenSec G L _ θ → ∀ (K' : Type) [Field K'] (i : K →+* K'),
      IsGenSec G L _ (SecAt.pull G L θ i) := by
  intro S G _ L hL g K _ x hP
  obtain ⟨P, α, -, hp, hw⟩ := hP
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp K) G L hL P x α hp hw K (𝟙 _) x
    (Category.id_comp x)
  have h0 : spMap (RingHom.id K) ≫ x = x := by rw [spMap_id, Category.id_comp]
  refine ⟨⟨_, isGenSec_of_univBasis he (RingHom.id K) h0⟩, fun θ hθ K' _ i => ?_⟩
  set e₀ := VVRank.pullS G _ (Over.homMk (spMap (RingHom.id K)) h0 : Over.mk x ⟶ Over.mk x) e with he₀
  obtain ⟨c, hc, -⟩ := he K (RingHom.id K) x h0 (SecM.ofSec G θ)
  obtain ⟨r, hr⟩ := (isGenSec_iff θ).1 hθ (SecM.ofSec G e₀)
  obtain ⟨c₀, -, hu⟩ := he K (RingHom.id K) x h0 (SecM.ofSec G e₀)
  have hrc : r * c = 1 := by
    have e1 : SecM.ofSec G e₀ = (r * c) • SecM.ofSec G e₀ := by
      conv_lhs => rw [hr, hc]
      rw [smul_smul]
    exact (hu _ e1).trans (hu 1 (one_smul _ _).symm).symm
  have hcu : IsUnit c := ⟨⟨c, r, by rw [mul_comm]; exact hrc, hrc⟩, rfl⟩
  have ha : IsUnit ((fnR x).symm c) := hcu.map (fnR x).symm
  have hb := he.smul_pull hL (RingHom.id K) h0 ha
  have eq : SecM.toSec G (fnR x ((fnR x).symm c) • pl (RingHom.id K) h0 (SecM.ofSec G e)) = θ := by
    rw [RingEquiv.apply_symm_apply, pl_ofSec, ← hc]
    rfl
  rw [eq] at hb
  exact isGenSec_of_univBasis hb i rfl

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.FibMove

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso (L.pull (g ≫ f)) ((L.pull f).pull g) :=
  LBIso.chartPull (RigidBundleGlue.chartPullComp L f g _ rfl) (chartPullId _)
    ⟨idIso _, idIso_isGen (pull_isLB (pull_isLB hL f) g)⟩

theorem polFib_move : ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (A : Over S') [GrpObj A] (L' : LB A.left) (f : S' ⟶ S) (φ : A.left ⟶ G.left), L.IsLB → L'.IsLB → IsGrpPullback A G f φ → LBIso L' (L.pull φ) → ∀ (g : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S'), (PolFib A L' g x ↔ PolFib G L g (x ≫ f)) ∧ ∀ (R' : Type) [CommRing R'] (i : R →+* R'), PolFib A L' g x → PolFib A L' g (spMap i ≫ x) := by
  intro S S' G _ L A _ L' f φ hL hL' hφ hLL' g R _ x
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨P, α, hg, hα, hPL⟩
    refine ⟨P, α ≫ φ, hg, hα.comp hφ, ?_⟩
    exact LBIso.trans P.isLB (pull_isLB hL' α) (pull_isLB hL _) hPL
      (LBIso.trans (pull_isLB hL' α) (pull_isLB (pull_isLB hL φ) α) (pull_isLB hL _)
        (RigidBundleGlue.LBIso.pull hLL' α) (lbIso_pull_comp hL φ α).symm)
  · rintro ⟨P, β, hg, hβ, hPL⟩
    have w : β ≫ G.hom = P.A.hom ≫ (x ≫ f) := hβ.1.w
    let α : P.A.left ⟶ A.left := hφ.1.lift β (P.A.hom ≫ x) (by rw [w, Category.assoc])
    have e₁ : α ≫ φ = β := hφ.1.lift_fst _ _ _
    have e₂ : α ≫ A.hom = P.A.hom ≫ x := hφ.1.lift_snd _ _ _
    refine ⟨P, α, hg, IsGrpPullback.cancel hφ (hβ.congr rfl e₁.symm) e₂, ?_⟩
    have h1 : LBIso P.L (L.pull (α ≫ φ)) := by rw [e₁]; exact hPL
    exact LBIso.trans P.isLB (pull_isLB hL _) (pull_isLB hL' α) h1
      (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL φ) α) (pull_isLB hL' α)
        (lbIso_pull_comp hL φ α) (RigidBundleGlue.LBIso.pull hLL'.symm α))
  · rintro R' _ i ⟨P, α, hg, hα, hPL⟩
    obtain ⟨P', ψ, hg', hψ, hPL'⟩ := exists_isPolFibre polBaseChange_holds i P
    refine ⟨P', ψ ≫ α, hg'.trans hg, hψ.comp hα, ?_⟩
    exact LBIso.trans P'.isLB (pull_isLB P.isLB ψ) (pull_isLB hL' _) hPL'.symm
      (LBIso.trans (pull_isLB P.isLB ψ) (pull_isLB (pull_isLB hL' α) ψ) (pull_isLB hL' _)
        (RigidBundleGlue.LBIso.pull hPL ψ) (lbIso_pull_comp hL' α ψ).symm)

end GlobalTheory.UMin.FibMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescend
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdUniq

theorem exists_spMap' {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ c : A →+* B, spMap c = f :=
  ⟨(Spec.preimage f).hom, by simp [spMap]⟩

theorem pCrd_iff {o R : Type} [CommRing o] [CommRing R] {n : ℕ} (x : Sp R ⟶ PSpace o n) (c : o →+* R)
    (hx : x ≫ PSpace.str o n = spMap c) (v : Fin (n + 1) → R) :
    PCrd x v ↔ ∃ hv : Ideal.span (Set.range v) = ⊤, x = ProjSpace.pt c v hv := by
  have h := ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) c x (by rw [Category.comp_id]; exact hx) v
  have h2 := RepBC.secCoord_pull (ProjSpace.O1 o n) (ProjSpace.coord o n) (𝟙 _) x v
  rw [Category.comp_id] at h2
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, Category.comp_id] at h
  exact h2.symm.trans h

theorem eq_of_pCrd {o R : Type} [CommRing o] [CommRing R] {n : ℕ} {x x' : Sp R ⟶ PSpace o n} {v : Fin (n + 1) → R}
    (hs : x ≫ PSpace.str o n = x' ≫ PSpace.str o n) (h : PCrd x v) (h' : PCrd x' v) : x = x' := by
  obtain ⟨c, hc⟩ := exists_spMap' (x ≫ PSpace.str o n)
  obtain ⟨hv, e⟩ := (pCrd_iff x c hc.symm v).1 h
  obtain ⟨hv', e'⟩ := (pCrd_iff x' c (hs ▸ hc.symm) v).1 h'
  rw [e, e']

theorem exists_ne_zero_of_pCrd {o K : Type} [CommRing o] [Field K] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v : Fin (n + 1) → K} (h : PCrd x v) : ∃ k, v k ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_spMap' (x ≫ PSpace.str o n)
  obtain ⟨hv, -⟩ := (pCrd_iff x c hc.symm v).1 h
  by_contra hn
  push_neg at hn
  have : Set.range v ⊆ {0} := by rintro _ ⟨k, rfl⟩; exact hn k
  have h0 : Ideal.span (Set.range v) = ⊥ := by
    rw [Ideal.span_eq_bot]; intro y hy; exact this hy
  rw [h0] at hv
  exact bot_ne_top hv

theorem scalar_of_pCrd {o K : Type} [CommRing o] [Field K] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v w : Fin (n + 1) → K} (hv : PCrd x v) (hw : PCrd x w) : ∃ a : K, a ≠ 0 ∧ ∀ j, w j = a * v j := by
  obtain ⟨u, hu⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hv).2.2 w hw
  exact ⟨u, u.ne_zero, hu⟩

theorem pCrd_of_map {o K K' : Type} [CommRing o] [Field K] [Field K'] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v : Fin (n + 1) → K} (i : K →+* K') (h : PCrd (spMap i ≫ x) (fun j => i (v j))) : PCrd x v := by
  obtain ⟨w, hw⟩ := FieldPoint.exists_secCoord o n K x
  have hw' := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw).1 K' i
  obtain ⟨u, hu⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw').2.2 _ h
  obtain ⟨k, hk⟩ := exists_ne_zero_of_pCrd h
  have hvk : v k ≠ 0 := fun e => hk (by simp only [e, map_zero])
  have hwk : w k ≠ 0 := fun e => hk (by rw [hu k]; simp only [e, map_zero, mul_zero])
  have hua : (u : K') = i (v k / w k) := by
    rw [map_div₀, eq_div_iff ((map_ne_zero i).2 hwk), hu k]
  have hvj : ∀ j, v j = (v k / w k) * w j := fun j => by
    apply i.injective
    rw [hu j, hua, map_mul]
  have hs := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw).2.1
    (Units.mk0 (v k / w k) (div_ne_zero hvk hwk))
  have e : (fun j => ((Units.mk0 (v k / w k) (div_ne_zero hvk hwk) : Kˣ) : K) * w j) = v :=
    funext fun j => (hvj j).symm
  rw [e] at hs
  exact hs

theorem main : (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x x' : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K), x ≫ PSpace.str o n = x' ≫ PSpace.str o n → PCrd x v → PCrd x' v → x = x') ∧ (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v w : Fin (n + 1) → K), PCrd x v → PCrd x w → ∃ a : K, a ≠ 0 ∧ ∀ j, w j = a * v j) ∧ ∀ (o K K' : Type) [CommRing o] [Field K] [Field K'] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (i : K →+* K'), PCrd (spMap i ≫ x) (fun j => i (v j)) → PCrd x v :=
  ⟨fun _ _ _ _ _ _ _ _ hs h h' => eq_of_pCrd hs h h',
   fun _ _ _ _ _ _ _ _ hv hw => scalar_of_pCrd hv hw,
   fun _ _ _ _ _ _ _ _ _ i h => pCrd_of_map i h⟩

end GlobalTheory.UMin.CrdUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapComp
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm

theorem pull_comp_entry {k m n : ℕ} (L : V n →L[ℂ] V m) (L' : V m →L[ℂ] V k) (b : Fin n) (a : Fin k) :
    (L' (L (coordVec b))).ofLp a = ∑ c, (L (coordVec b)).ofLp c * (L' (coordVec c)).ofLp a := by
  have hx : L (coordVec b) = ∑ c, (L (coordVec b)).ofLp c • (coordVec c : V m) := by
    simpa [coordVec] using (EuclideanSpace.basisFun (Fin m) ℂ).sum_repr (L (coordVec b)) |>.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  simp [map_smul, PiLp.smul_apply]
  simp [Pi.single_apply]

theorem pull_comp (k m n : ℕ) (L : V n →L[ℂ] V m) (L' : V m →L[ℂ] V k) (γ : Alt k) :
    pull (L'.comp L) γ = pull L (pull L' γ) := by
  have hM : (Matrix.fromBlocks (Matrix.of fun b a => ((L'.comp L) (coordVec b)).ofLp a) 0 0
        (Matrix.of fun b a => conj (((L'.comp L) (coordVec b)).ofLp a)) : Matrix (Fin n ⊕ Fin n) (Fin k ⊕ Fin k) ℂ) =
      Matrix.fromBlocks (Matrix.of fun b a => (L (coordVec b)).ofLp a) 0 0
        (Matrix.of fun b a => conj ((L (coordVec b)).ofLp a)) *
      Matrix.fromBlocks (Matrix.of fun b a => (L' (coordVec b)).ofLp a) 0 0
        (Matrix.of fun b a => conj ((L' (coordVec b)).ofLp a)) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · ext b a; simp only [Matrix.of_apply, ContinuousLinearMap.comp_apply, pull_comp_entry]
      simp [Matrix.mul_apply]
    · simp
    · simp
    · ext b a
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, Matrix.of_apply, ContinuousLinearMap.comp_apply, pull_comp_entry, map_sum, map_mul]
      simp [Matrix.mul_apply]
  simp only [pull]
  rw [hM, Matrix.toLin'_mul, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]

end GlobalTheory.CxForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfPeriodicRegularDifferencesRatioCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isReg_of_isReg_sub : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r → ∀ (h : Fin n → (Fin g → ℂ) → ℂ), (∀ k, DifferentiableOn ℂ (h k) (pre u.ex (W k))) → (∀ k (l : u.Λ), ∀ z ∈ pre u.ex (W k), h k (z + l) = h k z) → (∀ k j, IsReg u.ex (W k ⊓ W j) (h k - h j)) → ∀ k, IsReg u.ex (W k) (h k) := by
  intro A _ g L u hA n W r hr h hd hp hreg l
  obtain ⟨-, hdiff, -, hper, hinf, -, -, -, -, -, hbas, -⟩ := _root_.GlobalTheory.CechPer.pre_val_rules A g L u
  have hr' := hr
  obtain ⟨haff, -, hbo, -, hco⟩ := hr'
  have h1 : ∀ k, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ b : Γ(A.left, W k), ∀ z ∈ pre u.ex (A.left.basicOpen (r k l)),
      val u.ex (W k) b z = val u.ex (W k) (r k l) z ^ N * (h k - h l) z := fun k ↦
    _root_.GlobalTheory.ClearDen.exists_pow_mul_eq_val A g L u (W k) (haff k) (r k l) (h k - h l) (by rw [hbo]; exact hreg k l)
  choose N₀ hN₀ using h1
  set N : ℕ := Finset.univ.sup N₀ with hN
  have h2 := fun k ↦ hN₀ k N (Finset.le_sup (f := N₀) (Finset.mem_univ k))
  choose b hb using h2
  let σ : Fin n → (Fin g → ℂ) → ℂ := fun k z ↦
    val u.ex (W k) (r k l) z * (val u.ex (W k) (r k l) z ^ N * h k z - val u.ex (W k) (b k) z)
  have hin : ∀ k z, z ∈ pre u.ex (W k) → z ∈ pre u.ex (W l) → σ k z = val u.ex (W k) (r k l) z ^ (N + 1) * h l z := by
    intro k z hk hl
    have hz : z ∈ pre u.ex (A.left.basicOpen (r k l)) := by rw [hbo, hinf]; exact ⟨hk, hl⟩
    simp only [σ]
    rw [hb k z hz, Pi.sub_apply]
    ring
  have hout : ∀ k z, z ∉ pre u.ex (W l) → σ k z = 0 := by
    intro k z hl
    have hz : z ∉ pre u.ex (A.left.basicOpen (r k l)) := by rw [hbo, hinf]; exact fun hz ↦ hl hz.2
    rw [hbas, not_not] at hz
    simp only [σ]
    rw [hz, zero_mul]
  have hσ := _root_.GlobalTheory.CechPer.ratio_periodic_isReg A g L u hA n W r hr (N + 1) σ
    (fun k ↦ (hdiff _ (r k l)).mul ((((hdiff _ (r k l)).pow N).mul (hd k)).sub (hdiff _ (b k))))
    (fun k m z hz ↦ by simp only [σ]; rw [hper, hper, hp k m z hz])
    (fun k j z hk hj ↦ by
      by_cases hl : z ∈ pre u.ex (W l)
      · rw [hin k z hk hl, hin j z hj hl, hco k j l z hk hj]
        ring
      · rw [hout k z hl, hout j z hl, mul_zero]) l
  obtain ⟨c, hc⟩ := hσ
  refine ⟨c, fun z hz ↦ ?_⟩
  have hne : val u.ex (W l) (r l l) z ≠ 0 := by
    rw [← hbas, hbo, hinf]; exact ⟨hz, hz⟩
  have hone : val u.ex (W l) (r l l) z = 1 :=
    (mul_right_cancel₀ hne ((_root_.one_mul _).trans (hco l l l z hz hz))).symm
  rw [← hc z hz, hin l z hz hz, hone, one_pow, _root_.one_mul]

end GlobalTheory.CechPer
end

