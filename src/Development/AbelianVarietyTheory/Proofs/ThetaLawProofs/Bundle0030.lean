module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TopLeTranslate
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KosBlockMulKosD
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BoxProductsBasisSpanPowObjSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxProducts_basis_span_powObj_sections : ∀ (K : Type) [Field K] (x : KeyIn K) (m N : ℕ) (b : Fin N → RR x m), IsBasis x b → ∀ (n : ℕ) (s : LB.Sec (LB.LinComb x.P.L (K := Fin n) (fun c => (Out.powPr x.P.A c).left) (fun _ => (m : ℤ)))), ∃ q : (Fin n → Fin N) → K, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj x.P.A n).left) (z : Z) J, Good x.P.L z J → sval s r z J = ∑ I, gs r z ⊤ (cst (Out.powObj x.P.A n).hom ⊤ (q I)) * ∏ c, gs (r ≫ (Out.powPr x.P.A c).left) z (x.P.L.U (J (r ≫ (Out.powPr x.P.A c).left))) ((b (I c)).f (J (r ≫ (Out.powPr x.P.A c).left))) := by
  first | exact @GlobalTheory.BoxSpan.boxProducts_span | exact GlobalTheory.BoxSpan.boxProducts_span | (intros; apply GlobalTheory.BoxSpan.boxProducts_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBScale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyScaleLift

theorem exists_keyPB_scale : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (y : KeyIn R) (x : KeyIn R') (a : Rˣ) (M : Matrix (Fin x.P.g) (Fin x.P.g) R), KeyPB x y f → IsUnit M.det → ∃ y₁ : KeyIn R, ∀ (t : x.P.L.Sec) (ht : _) (v : Fin x.P.g → (epsR R' ⟶ x.P.A)) (hv : _), (∀ i, t.f i = constFn x.P.A.hom _ (f a) * x.th.f i) → (∀ i, IsLieComb (fun k => f (M i k)) x.v (v i)) → KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, t, ht, v, hv⟩ y₁ f := by
  intro R R' _ _ f y x a M h hM
  obtain ⟨e⟩ : Nonempty (x.P.g = y.P.g) := by
    obtain ⟨_, _, _, hg, _⟩ := h
    exact ⟨hg⟩
  haveI := y.P.isAb.comm
  let N : Matrix (Fin y.P.g) (Fin y.P.g) R := Matrix.reindex (finCongr e) (finCongr e) M
  have hN : IsUnit N.det := by rwa [Matrix.det_reindex_self]
  obtain ⟨ex, -, -, -, bas⟩ := GlobalTheory.LieComb.lieComb_algebra R y.P.A y.P.g y.v y.basis.1
  choose v₁ hv₁ using fun i => (ex (N i)).exists
  obtain ⟨s, hs, -, hle⟩ := exists_sec_div y.P.A.hom a.inv_mul y.th
  refine ⟨⟨y.P, y.g_pos, y.rig, y.rig_gen, s, fun p => (y.th_ne p).imp fun z hz => ⟨hz.1, hle hz.2⟩, v₁,
    (bas N v₁ y.basis hv₁).2 hN⟩, fun t ht v hv h₁ h₂ => ?_⟩
  exact KeyPBScale.keyPB_scale R R' f y.P y.g_pos y.rig y.rig_gen y.th y.th_ne y.v y.basis s _ v₁ _ a N x.P e
    x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis t ht v hv hs hv₁ h₁ h₂ h

end GlobalTheory.KeyScaleLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantFromIntersectionUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KaUnique

theorem exists_perm {K : Type} [Field K] {x : KeyIn K} {n d : ℕ} {s : Fin x.P.g → RR x n} {z z' : Fin d → Pt x}
    {ch ch' : Fin d → x.P.L.ι} (hz : EtZ x s z ch) (hz' : EtZ x s z' ch') :
    ∃ σ : Equiv.Perm (Fin d), ∀ a, z' (σ a) = z a := by
  let p : Sp K := IsLocalRing.closedPoint K
  have hs : ∀ q q' : Sp K, q = q' := fun q q' => Subsingleton.elim (α := PrimeSpectrum K) q q'
  have h1 : ∀ a, ∃ a', z' a' = z a := by
    intro a
    obtain ⟨a', q, hq⟩ := hz'.2.2.2.2 ((z a).left p) (fun i hi => by
      obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
      have hcU : ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U c := fun q _ => by
        rw [hs q p]; exact x.P.A.left.basicOpen_le _ hc
      have e := valT_sec (T := K) (z a).left x.P.L c (ch a) hcU (hz.1 a) n (s i)
      erw [hz.2.1 a i, mul_zero, valT_eq _ _ hcU] at e
      have e1 : IsUnit (evalHom (T := K) (z a).left (x.P.L.U c) hcU ((s i).f c)) ↔
          IsUnit (((show Sp K ⟶ x.P.A.left from (z a).left).appLE (x.P.L.U c) ⊤ hcU).hom ((s i).f c)) :=
        isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv _
      have e2 := Scheme.basicOpen_appLE (show Sp K ⟶ x.P.A.left from (z a).left) ⊤ (x.P.L.U c) hcU ((s i).f c)
      have e3 : IsUnit (((show Sp K ⟶ x.P.A.left from (z a).left).appLE (x.P.L.U c) ⊤ hcU).hom ((s i).f c)) := by
        apply RingedSpace.isUnit_of_isUnit_germ
        intro q hq
        have : q ∈ (Sp K).basicOpen
            (((show Sp K ⟶ x.P.A.left from (z a).left).appLE (x.P.L.U c) ⊤ hcU).hom ((s i).f c)) := by
          erw [e2]; rw [hs q p]; exact ⟨trivial, hc⟩
        exact ((Sp K).mem_basicOpen _ q hq).1 this
      exact (e1.2 e3).ne_zero e)
    exact ⟨a', Over.OverMorphism.ext (section_ext x.P.A.hom _ _ (Over.w (z' a')) (Over.w (z a)) q p hq)⟩
  choose f hf using h1
  have hinj : Function.Injective f := fun a a' e => by
    by_contra hne
    exact hz.2.2.2.1 a a' hne p (by rw [← hf a, ← hf a', e])
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

theorem degree_compare (hL : Out.Laws) {K : Type} [Field K] [CharZero K] (x : KeyIn K) {n l d : ℕ}
    {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ}
    (hal : ∀ m, (al m).transpose * al m = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (hl : x.P.g * n < l)
    {s : Fin x.P.g → RR x n} {z z' : Fin d → Pt x} {ch ch' : Fin d → x.P.L.ι} (hz : EtZ x s z ch) (hz' : EtZ x s z' ch')
    (σ : Equiv.Perm (Fin d)) (ga : Fin d → Kˣ)
    (hga : ∀ a (r : RR x (l - 0 * n)), valT (T := K) (z a).left (x.P.L.U (ch a)) (r.f (ch a)) =
      (ga a).val ^ (l - 0 * n) * valT (T := K) (z' (σ a)).left (x.P.L.U (ch' (σ a))) (r.f (ch' (σ a))))
    {b b' : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)} {t t' : Kˣ} {lam lam' : ℕ → Kˣ}
    (hb : ∀ j ≤ x.P.g, IsBasis x (b j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b j) (lam j))
    (hb' : ∀ j ≤ x.P.g, IsBasis x (b' j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b' j) (lam' j))
    (ht : KosVal x l s z ch b t) (ht' : KosVal x l s z' ch' b' t') :
    ∃ be : ℕ → Kˣ, t' = t * (∏ a, ga a) ^ (-2 * (l : ℤ)) * 1 ^ 2 *
        ∏ j ∈ Finset.range (x.P.g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (x.P.g.choose j : ℤ)) ∧
      ∀ j ≤ x.P.g, lam' j = lam j * be j ^ (-8 * ((l - j * n) ^ (3 * x.P.g + 2) : ℕ) : ℤ) *
        1 ^ (8 * (l - j * n) ^ (4 * x.P.g + 2)) := by
  have hB : ∀ j, ∃ B : (Matrix (Fin ((l - j * n) ^ x.P.g)) (Fin ((l - j * n) ^ x.P.g)) K)ˣ, j ≤ x.P.g →
      ∀ k, IsComb x.P.A.hom x.P.L (fam x (b j)) (fun k' => B.val k' k) (fam x (b' j) k) := fun j => by
    by_cases hj : j ≤ x.P.g
    · obtain ⟨B, hB⟩ := exists_change (hb j hj).1 (hb' j hj).1
      exact ⟨B, fun _ => hB⟩
    · exact ⟨1, fun h => absurd h hj⟩
  choose B hB using hB
  obtain ⟨m, hm, ht⟩ := ht
  obtain ⟨m', hm', ht'⟩ := ht'
  let P : Matrix (Fin d) (Fin d) K := (Matrix.diagonal fun a => (ga a).val ^ (l - 0 * n)).submatrix id σ.symm
  have hP : P.det ^ 2 = (((∏ a, ga a) ^ (2 * l) : Kˣ) : K) := by
    simp only [P]
    rw [Matrix.det_permute', Matrix.det_diagonal, mul_pow, Finset.prod_pow, ← pow_mul]
    have : ((Equiv.Perm.sign σ.symm : ℤ) : K) ^ 2 = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]
    rw [this]
    simp [mul_comm]
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2
    ((isUnit_pow_iff two_ne_zero).1 (hP ▸ Units.isUnit _))
  obtain ⟨t'', h1, h2⟩ := GlobalTheory.KeyKa.torsSq_kosD_conj K x.P.g d (fun j => (l - j * n) ^ x.P.g) m m' _
    (fun j => Matrix.of fun a k => valT (T := K) (z' a).left (x.P.L.U (ch' a)) ((b' j k).f (ch' a))) B hPu.unit t
    (fun i j hj => by
      ext a k
      have e1 := IsComb.mulVec' (hB j hj.le) (isMul_comb hm' i j hj k)
      have e2 := IsComb.mulVec (isMul_comb hm i j hj) (hB (j + 1) hj k)
      exact congrFun (comb_unique (hb j hj.le).1 e1 e2) a)
    (by
      ext a k
      have e1 := (hB 0 (Nat.zero_le _) k).valT (z a).left (Over.w (z a)) (ch a) (hz.1 a)
      refine Eq.trans ?_ e1
      refine Eq.trans ?_ (hga a (b' 0 k)).symm
      rw [IsUnit.unit_spec, Matrix.mul_apply, Finset.sum_eq_single (σ a)]
      · simp [P]
      · intro a' _ h
        have : a ≠ σ.symm a' := fun e => h (by rw [e, Equiv.apply_symm_apply])
        simp [P, Matrix.diagonal_apply_ne _ this]
      · intro h; exact absurd (Finset.mem_univ _) h)
    (isCx_of_isMul hm (fun j hj => (hb j hj).1) hz) ht
  have h3 : t'' = t' := Units.ext (GlobalTheory.TorsionUnique.torsSq_unique K _ _ _ _ _
    (isCx_of_isMul hm' (fun j hj => (hb' j hj).1) hz') h1 ht').1
  subst h3
  have h4 : Matrix.GeneralLinearGroup.det hPu.unit ^ 2 = (∏ a, ga a) ^ (2 * l) := Units.ext hP
  refine ⟨fun j => Matrix.GeneralLinearGroup.det (B j), ?_, fun j hj => ?_⟩
  · rw [h4] at h2
    rw [one_pow, _root_.mul_one, mul_right_comm, ← h2, neg_mul, zpow_neg]
    have : (∏ a, ga a) ^ (2 * (l : ℤ)) = (∏ a, ga a) ^ (2 * l) := by
      rw [← zpow_natCast]; push_cast; rfl
    rw [this, mul_inv_cancel_right]
  · rw [one_pow, _root_.mul_one]
    have hpos : l - j * n ≠ 0 := by
      have : j * n ≤ x.P.g * n := Nat.mul_le_mul_right _ hj
      omega
    exact GlobalTheory.BoxDetUnique.isSquareDetComparison_eq_mul_det_pow_of_basis_change hL K x (l - j * n) _ (b j) (b' j) (B j) _ _ (Nat.cast_ne_zero.2 hpos) (hal _) (hb j hj).1
      (hB j hj) (hb j hj).2 (hb' j hj).2

theorem tComb_congr {R : Type} [CommRing R] (g n l Pr : ℕ) (t : Rˣ) {lam mu : ℕ → Rˣ} (h : ∀ j ≤ g, lam j = mu j) :
    tComb g n l Pr t lam = tComb g n l Pr t mu := by
  unfold tComb
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]

theorem kaVal_unique : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin x.P.g → RR x n) (κ κ' : Kˣ), admitted x.P.g n l l' al → KaVal x n l l' al s κ → KaVal x n l l' al s κ' → κ = κ' := by
  intro hL K _ _ x n l l' al s κ κ' ⟨_, hl, hl', hal⟩
    ⟨z, ch, b₁, b₂, t₁, t₂, J, lam₁, lam₂, hz, hJ, hb₁, hb₂, ht₁, ht₂, hκ⟩
    ⟨z', ch', b₁', b₂', t₁', t₂', J', lam₁', lam₂', hz', hJ', hb₁', hb₂', ht₁', ht₂', hκ'⟩
  obtain ⟨σ, hσ⟩ := exists_perm hz hz'
  have hc : ∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch' (σ a)) := fun a => hσ a ▸ hz'.1 (σ a)
  let ga := fun a => trU (T := K) (z a).left x.P.L (ch a) (ch' (σ a)) (hz.1 a) (hc a)
  have hga : ∀ (k : ℕ) a (r : RR x k), valT (T := K) (z a).left (x.P.L.U (ch a)) (r.f (ch a)) =
      (ga a).val ^ k * valT (T := K) (z' (σ a)).left (x.P.L.U (ch' (σ a))) (r.f (ch' (σ a))) := fun k a r => by
    rw [hσ a]
    exact valT_sec (T := K) (z a).left x.P.L _ _ (hz.1 a) (hc a) k r
  obtain ⟨be₁, e₁, f₁⟩ := degree_compare hL x hal hl hz hz' σ ga (hga _) hb₁ hb₁' ht₁ ht₁'
  obtain ⟨be₂, e₂, f₂⟩ := degree_compare hL x hal (hl.trans hl') hz hz' σ ga (hga _) hb₂ hb₂' ht₂ ht₂'
  have eJ : J' = J * (∏ a, ga a) ^ (-((x.P.g * n : ℕ) : ℤ)) * 1 ^ 2 := by
    rw [one_pow, _root_.mul_one, zpow_neg, zpow_natCast, eq_mul_inv_iff_mul_eq]
    apply Units.ext
    rw [Units.val_mul, hJ, hJ', ← Equiv.prod_comp σ, Units.val_pow_eq_pow_val, Units.coe_prod, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    have h0 := hz'.2.1 (σ a)
    rw [hσ a] at h0 ⊢
    rw [jac_chart x s (z a) (ch a) (ch' (σ a)) (hz.1 a) (hc a) h0, mul_comm]
  have key := GlobalTheory.kaForm_homogeneous K x.P.g n l l' t₁ t₂ J (∏ a, ga a) 1 1 lam₁ lam₂ be₁ be₂ hl hl'
  rw [one_pow (8 * kaExp _ _ _ _), _root_.mul_one, ← e₁, ← e₂, ← eJ] at key
  rw [hκ, hκ', ← key]
  unfold kaForm
  rw [tComb_congr _ _ _ _ t₁' f₁, tComb_congr _ _ _ _ t₂' f₂]

end GlobalTheory.KaUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SimilitudeGeneratorEqExpInFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta

theorem span_single_block_eq_top {V : Type} [AddCommGroup V] [Module ℝ V] {Λ : Set V} (h : Submodule.span ℝ Λ = ⊤) :
    Submodule.span ℝ {s : Fin 4 → V | ∃ c, ∃ l ∈ Λ, s = Pi.single c l} = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  rw [← Finset.univ_sum_single y]
  refine Submodule.sum_mem _ fun c _ => ?_
  have hz : y c ∈ Submodule.span ℝ Λ := h ▸ Submodule.mem_top
  generalize y c = v at hz
  induction hz using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span ⟨c, v, hv, rfl⟩
  | zero => rw [Pi.single_zero]; exact Submodule.zero_mem _
  | add v v' _ _ hv hv' => rw [Pi.single_add]; exact Submodule.add_mem _ hv hv'
  | smul r v _ hv => rw [Pi.single_smul]; exact Submodule.smul_mem _ r hv

theorem ex_zsmul_eq_zpow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (s : ℤ) (z : Fin g → ℂ) :
    u.ex (s • z) = u.ex z ^ s :=
  map_zpow (MonoidHom.mk' (fun z : Multiplicative (Fin g → ℂ) => u.ex z.toAdd) fun _ _ => u.ex_add _ _)
    (Multiplicative.ofAdd z) s

theorem comp_alMap_ex {g : ℕ} (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (al : Matrix (Fin 4) (Fin 4) ℤ) (r : Fin 4)
    (t : Fin g → ℂ) (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4)
    (hpt : ∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) :
    pt ≫ alMap x al r (u.ex t) = u.ex (∑ c, al r c • y c + t) := by
  have e₀ : pt ≫ toUnit _ = 𝟙 _ := toUnit_unique _ _
  simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul,
    GrpObj.comp_zpow, MonObj.comp_one, hpt, reassoc_of% e₀, Fin.sum_univ_succ, Fin.sum_univ_zero, u.ex_add, ex_zsmul_eq_zpow,
    GlobalTheory.PowUnif.ex_zero]

theorem simil_generator_eq_exp : ∀ (g m : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ), charHalf g a b → Wit x h u τ a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∀ (k n : Fin 4 → Fin g → ℤ) (ξ : Fin 4 → Pt x), (∀ r, ξ r = u.ex (tors τ al m k n r)) → ∀ w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))), w.IsGen → ∃ C : ℂ, C ≠ 0 ∧ ∀ (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4), (∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) → ∀ j : Fin 4 ⊕ Fin 4 → x.P.L.ι, (∀ r, ⊤ ≤ (u.ex (∑ c, al r c • y c + tors τ al m k n r)).left ⁻¹ᵁ x.P.L.U (j (Sum.inl r))) → (∀ c, ⊤ ≤ (u.ex (y c)).left ⁻¹ᵁ x.P.L.U (j (Sum.inr c))) → valAt' pt.left (LB.wchart x.P.L (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) j) (w.s j).val * Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c) = C * ((∏ r, u.fr (j (Sum.inl r)) (∑ c, al r c • y c + tors τ al m k n r)) * ∏ c, u.fr (j (Sum.inr c)) (y c) ^ (-(m : ℤ))) := by
  intro g m x h u τ a b al hab hW hm hal k n ξ hξ w hw
  obtain rfl : ξ = fun r => u.ex (tors τ al m k n r) := funext hξ
  let P : (Fin 4 → Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4) := fun y =>
    (Out.powIsLimit x.P.A 4).lift (Fan.mk _ fun c => u.ex (y c))
  have hP : ∀ y c, P y ≫ Out.powPr x.P.A c = u.ex (y c) := fun y c =>
    (Out.powIsLimit x.P.A 4).fac (Fan.mk _ fun c => u.ex (y c)) ⟨c⟩
  have hPu : ∀ (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4),
      (∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) → pt = P y := fun y pt hpt =>
    (Out.powIsLimit x.P.A 4).hom_ext fun ⟨c⟩ => (hpt c).trans (hP y c).symm
  have hd : GlobalTheory.PowUnif.IsHolFamily (fun z => (u.ex z).left) := u.hol
  let z : Fin 4 ⊕ Fin 4 → (Fin 4 → Fin g → ℂ) → Fin g → ℂ :=
    Sum.elim (fun r y => ∑ c, al r c • y c + tors τ al m k n r) (fun c y => y c)
  obtain ⟨T, hT, hT0, hTv⟩ := _root_.GlobalTheory.exists_entire_generator_div_frames x.P.A x.P.L g u x.P.isLB _ _ _ _ w hw (Fin 4 → Fin g → ℂ)
    (fun y => (P y).left) z
    (GlobalTheory.PowUnif.isHolFamily_powObj _ 4 P fun c => by
      simp only [hP]
      exact hd.precomp (T := fun y : Fin 4 → Fin g → ℂ => y c) (by fun_prop))
    (by
      rintro (r | c)
      · change Differentiable ℂ fun y : Fin 4 → Fin g → ℂ => ∑ c, al r c • y c + tors τ al m k n r
        fun_prop
      · change Differentiable ℂ fun y : Fin 4 → Fin g → ℂ => y c
        fun_prop)
    (by
      rintro y (r | c)
      · exact congrArg (·.left) (comp_alMap_ex x u al r _ y (P y) (hP y))
      · exact congrArg (·.left) (hP y c))
  let ee : (Fin 4 → Fin g → ℂ) → ℂ := fun y =>
    Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c)
  have hee : Differentiable ℂ ee := by
    simp only [ee, dotProduct]
    fun_prop
  have hper : ∀ y, ∀ s ∈ {s : Fin 4 → Fin g → ℂ | ∃ c, ∃ l ∈ (u.Λ : Set (Fin g → ℂ)), s = Pi.single c l},
      T (y + s) * ee (y + s) = T y * ee y := by
    rintro y _ ⟨c, l, hl, rfl⟩
    obtain ⟨k₀, n₀, hl'⟩ := (hW.2.2.1 l).1 hl
    obtain rfl : l = lat τ k₀ n₀ := hl'
    have hlat : ∀ (k n : Fin g → ℤ) (v : Fin g → ℂ), u.ex (v + lat τ k n) = u.ex v := fun k n v => by
      rw [u.ex_add, (u.ker (lat τ k n)).2 ((hW.2.2.1 _).2 ⟨k, n, rfl⟩), _root_.mul_one]
    set y' := y + Pi.single c (lat τ k₀ n₀) with hy'
    have hz₁ : ∀ r, z (Sum.inl r) y' = z (Sum.inl r) y + lat τ (al r c • k₀) (al r c • n₀) := fun r => by
      simp only [z, Sum.elim_inl, hy', Pi.add_apply, smul_add, Finset.sum_add_distrib, lat_zsmul]
      rw [Finset.sum_eq_single c (f := fun c' => al r c' • (Pi.single c (lat τ k₀ n₀) : Fin 4 → Fin g → ℂ) c')
        (fun c' _ hc => by rw [Pi.single_eq_of_ne hc, smul_zero]) (by simp),
        Pi.single_eq_same]
      abel
    have hz₂ : y' c = y c + lat τ k₀ n₀ := by simp [hy']
    have hz₃ : ∀ c', c' ≠ c → y' c' = y c' := fun c' hc => by simp [hy', Pi.single_eq_of_ne hc]
    have hex : ∀ q, u.ex (z q y') = u.ex (z q y) := by
      rintro (r | c')
      · rw [hz₁, hlat]
      · change u.ex (y' c') = u.ex (y c')
        by_cases hc : c' = c
        · rw [hc, hz₂, hlat]
        · rw [hz₃ c' hc]
    have hPP : P y' = P y := hPu y _ fun c' => (hP y' c').trans (hex (Sum.inr c'))
    choose j hj using fun q => GlobalTheory.PowUnif.exists_chart x.P.isLB (u.ex (z q y)).left
    have hj' : ∀ q, ⊤ ≤ (u.ex (z q y')).left ⁻¹ᵁ x.P.L.U (j q) := fun q => by rw [hex]; exact hj q
    have e₁ := hTv y j hj
    have e₂ := hTv y' j hj'
    rw [hPP, e₁] at e₂
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_one] at e₂
    have f₁ : ∏ r, u.fr (j (Sum.inl r)) (z (Sum.inl r) y) =
        (∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) *
          ∏ r, u.fr (j (Sum.inl r)) (z (Sum.inl r) y') := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [hz₁]
      exact _root_.GlobalTheory.SimilTheta.Frame.frame_eq_aut_mul g x h u τ a b hab hW _ _ _ _ (hj _)
    have f₂ : ∏ c', u.fr (j (Sum.inr c')) (z (Sum.inr c') y) ^ (-(m : ℤ)) =
        aut τ a b k₀ n₀ (y c) ^ (-(m : ℤ)) * ∏ c', u.fr (j (Sum.inr c')) (z (Sum.inr c') y') ^ (-(m : ℤ)) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
        ← _root_.mul_assoc, ← mul_zpow]
      refine congrArg₂ (· * ·) (congrArg (· ^ _) ?_) (Finset.prod_congr rfl fun c' hc => ?_)
      · change u.fr _ (y c) = _ * u.fr _ (y' c)
        rw [hz₂]
        exact _root_.GlobalTheory.SimilTheta.Frame.frame_eq_aut_mul g x h u τ a b hab hW _ _ _ _ (hj (Sum.inr c))
      · change u.fr _ (y c') ^ _ = u.fr _ (y' c') ^ _
        rw [hz₃ c' (Finset.ne_of_mem_erase hc)]
    have n₁ : ∏ r, u.fr (j (Sum.inl r)) (z (Sum.inl r) y') ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun r _ => u.fr_ne _ _ (hj' _)
    have n₂ : ∏ c', u.fr (j (Sum.inr c')) (z (Sum.inr c') y') ^ (-(m : ℤ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (u.fr_ne _ _ (hj' _))
    have e₃ : T y' = T y * (∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) *
        aut τ a b k₀ n₀ (y c) ^ (-(m : ℤ)) := by
      rw [f₁, f₂] at e₂
      refine mul_right_cancel₀ (mul_ne_zero n₁ n₂) (e₂.symm.trans ?_)
      ring
    have e₄ : ee y' = ee y * Complex.exp (2 * Real.pi * Complex.I * ((fun i => (n c i : ℂ)) ⬝ᵥ lat τ k₀ n₀)) := by
      simp only [ee, hy', Pi.add_apply, dotProduct_add, Finset.sum_add_distrib, mul_add, Complex.exp_add]
      rw [Finset.sum_eq_single c (f := fun c' => (fun i => (n c' i : ℂ)) ⬝ᵥ
          (Pi.single c (lat τ k₀ n₀) : Fin 4 → Fin g → ℂ) c')
        (fun c' _ hc => by rw [Pi.single_eq_of_ne hc, dotProduct_zero]) (by simp), Pi.single_eq_same]
    have e₅ : (∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) * _ = _ :=
      (aut_similitude_and_mul g m τ a b al hab hW.1 hm hal).1 k n y c k₀ n₀
    have n₃ := pow_ne_zero m (aut_ne_zero τ a b k₀ n₀ (y c))
    rw [e₃, e₄, zpow_neg, zpow_natCast]
    calc _ = T y * ee y * ((∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) *
          Complex.exp (2 * Real.pi * Complex.I * ((fun i => (n c i : ℂ)) ⬝ᵥ lat τ k₀ n₀))) *
          (aut τ a b k₀ n₀ (y c) ^ m)⁻¹ := by ring
      _ = _ := by rw [e₅, mul_inv_cancel_right₀ n₃]
  have hc := GlobalTheory.entire_apply_eq_of_periodic_of_span_real (F := fun y => T y * ee y) (hT.mul hee)
    (span_single_block_eq_top u.full) hper
  refine ⟨T 0 * ee 0, mul_ne_zero (hT0 0) (Complex.exp_ne_zero _), fun y pt hpt j hj₁ hj₂ => ?_⟩
  obtain rfl := hPu y pt hpt
  have e₁ := hTv y j (by rintro (r | c); exacts [hj₁ r, hj₂ c])
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_one, z] at e₁
  rw [← hc y 0]
  refine (congrArg (· * ee y) e₁).trans ?_
  ring

end GlobalTheory.SimilTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaGeneratorPullbackMulConstInFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

namespace GlobalTheory.SimilTheta

theorem ex_nsmul_eq_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (m : ℕ)
    (z : Fin g → ℂ) : u.ex ((m : ℤ) • z) = u.ex z ^ m := by
  rw [natCast_zsmul]
  induction m with
  | zero => simpa using GlobalTheory.CubeValues.ex_zero u
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_comp_id_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (m : ℕ)
    (z : Fin g → ℂ) : u.ex z ≫ (𝟙 A) ^ m = u.ex ((m : ℤ) • z) := by
  rw [ex_nsmul_eq_pow, MonObj.comp_pow, Category.comp_id]

theorem generator_mul_const_in_frames : ∀ (g m : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ), charHalf g a b → Wit x h u τ a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∀ mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]), mu.IsGen → ∃ C : ℂ, C ≠ 0 ∧ ∀ (z : Fin g → ℂ) (j : Fin 2 → x.P.L.ι), ⊤ ≤ (u.ex ((m : ℤ) • z)).left ⁻¹ᵁ x.P.L.U (j 0) → ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U (j 1) → valAt' (u.ex z).left (LB.wchart x.P.L ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] j) (mu.s j).val = C * (u.fr (j 0) ((m : ℤ) • z) * u.fr (j 1) z ^ (-(m : ℤ) ^ 2)) := by
  intro g m x h u τ a b al hab hW hm hal mu hmu
  obtain ⟨T, hT, hT0, hTv⟩ := _root_.GlobalTheory.exists_entire_generator_div_frames x.P.A x.P.L g u x.P.isLB x.P.A.left (Fin 2)
    ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2] mu hmu (Fin g → ℂ) (fun z => (u.ex z).left)
    ![fun z => (m : ℤ) • z, fun z => z] u.hol
    (Fin.forall_fin_two.2 ⟨differentiable_id.const_smul (m : ℤ), differentiable_id⟩)
    (fun e => Fin.forall_fin_two.2 ⟨congrArg (fun q => q.left) (ex_comp_id_pow u m e), Category.comp_id _⟩)
  have hv : ∀ (z : Fin g → ℂ) (j : Fin 2 → x.P.L.ι), ⊤ ≤ (u.ex ((m : ℤ) • z)).left ⁻¹ᵁ x.P.L.U (j 0) →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U (j 1) →
      valAt' (u.ex z).left (LB.wchart x.P.L ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] j) (mu.s j).val =
        T z * (u.fr (j 0) ((m : ℤ) • z) * u.fr (j 1) z ^ (-(m : ℤ) ^ 2)) := fun z j h0 h1 => by
    refine (hTv z j (Fin.forall_fin_two.2 ⟨h0, h1⟩)).trans ?_
    rw [Fin.prod_univ_two]
    exact congrArg (fun t => T z * (t * u.fr (j 1) z ^ (-(m : ℤ) ^ 2))) (zpow_one _)
  have hper : ∀ z, ∀ l ∈ (u.Λ : Set (Fin g → ℂ)), T (z + l) = T z := by
    intro z l hl
    obtain ⟨k, n, hkn⟩ := (hW.2.2.1 l).1 hl
    obtain rfl : l = lat τ k n := hkn
    obtain ⟨i0, h0⟩ := GlobalTheory.PowUnif.exists_chart x.P.isLB (u.ex ((m : ℤ) • z)).left
    obtain ⟨i1, h1⟩ := GlobalTheory.PowUnif.exists_chart x.P.isLB (u.ex z).left
    have e1 : u.ex (z + lat τ k n) = u.ex z := GlobalTheory.CubeValues.ex_add_period u z _ hl
    have e0 : u.ex ((m : ℤ) • (z + lat τ k n)) = u.ex ((m : ℤ) • z) := by
      rw [ex_nsmul_eq_pow, e1, ex_nsmul_eq_pow]
    have A1 := hv z ![i0, i1] h0 h1
    have A2 := hv (z + lat τ k n) ![i0, i1] (by rw [e0]; exact h0) (by rw [e1]; exact h1)
    rw [e1, A1] at A2
    have n0 := u.fr_ne i0 ((m : ℤ) • (z + lat τ k n)) (by rw [e0]; exact h0)
    have n1 := u.fr_ne i1 (z + lat τ k n) (by rw [e1]; exact h1)
    have f0 := _root_.GlobalTheory.SimilTheta.Frame.frame_eq_aut_mul g x h u τ a b hab hW ((m : ℤ) • k) ((m : ℤ) • n) i0 _ h0
    have f1 := _root_.GlobalTheory.SimilTheta.Frame.frame_eq_aut_mul g x h u τ a b hab hW k n i1 _ h1
    rw [lat_zsmul, ← smul_add, (GlobalTheory.SimilTheta.aut_similitude_and_mul g m τ a b al hab hW.1 hm hal).2] at f0
    change T z * (u.fr i0 _ * u.fr i1 _ ^ _) = T _ * (u.fr i0 _ * u.fr i1 _ ^ _) at A2
    rw [f0, f1] at A2
    have na := aut_ne_zero τ a b k n z
    have hp : (-(m : ℤ) ^ 2) = -((m ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [hp, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_pow] at A2
    field_simp at A2
    exact A2.symm
  refine ⟨T 0, hT0 0, fun z j h0 h1 => ?_⟩
  rw [hv z j h0 h1, GlobalTheory.entire_apply_eq_of_periodic_of_span_real hT u.full hper z 0]

end GlobalTheory.SimilTheta
end

