module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CmpValBaseChangeSimilitude
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KaBaseChange

theorem torsSq_diag {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R)
    (ga : Ix → Rˣ) (t : R) (H : TorsSq deg D t) :
    TorsSq deg (Matrix.diagonal (fun p => (ga p : R)) * D * Matrix.diagonal (fun p => (((ga p)⁻¹ : Rˣ) : R)))
      (t * ((∏ p : {p // Even (deg p)}, (ga p.1 : R)) * ∏ p : {p // ¬ Even (deg p)}, (((ga p.1)⁻¹ : Rˣ) : R)) ^ 2) := by
  obtain ⟨h, h₁, h₂, e, rfl⟩ := H
  set G := Matrix.diagonal (fun p => (ga p : R)) with hG
  set G' := Matrix.diagonal (fun p => (((ga p)⁻¹ : Rˣ) : R)) with hG'
  have hGG : G * G' = 1 := by
    rw [hG, hG', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    simp
  have hGG' : G' * G = 1 := mul_eq_one_comm.mp hGG
  refine ⟨G * h * G', fun p q hpq => ?_, ?_, e, ?_⟩
  · rw [hG, hG', Matrix.mul_diagonal, Matrix.diagonal_mul, h₁ p q hpq, mul_zero, zero_mul]
  · calc G * D * G' * (G * h * G') + G * h * G' * (G * D * G')
        = G * (D * (G' * G) * h + h * (G' * G) * D) * G' := by noncomm_ring
      _ = 1 := by rw [hGG', Matrix.mul_one, Matrix.mul_one, h₂, Matrix.mul_one, hGG]
  · have e₁ : G * D * G' + G * h * G' = G * (D + h) * G' := by noncomm_ring
    have e₂ : (G * (D + h) * G').submatrix (fun p : {p // Even (deg p)} => p.1) (fun p => (e p).1) =
        Matrix.diagonal (fun p : {p // Even (deg p)} => (ga p.1 : R)) *
          (D + h).submatrix (fun p : {p // Even (deg p)} => p.1) (fun p => (e p).1) *
          Matrix.diagonal (fun p : {p // Even (deg p)} => (((ga (e p).1)⁻¹ : Rˣ) : R)) := by
      ext p q
      simp only [hG, hG', Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [e₁, e₂, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
      Equiv.prod_comp e (fun p => (((ga p.1)⁻¹ : Rˣ) : R))]
    ring

theorem torsSq_kosD_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {g d : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (ev' : ∀ j, Matrix (Fin d) (Fin (N j)) R') (c : Fin d → R'ˣ) (t : R)
    (hev : ∀ a k, ev' 0 a k * (c a : R') = f (ev 0 a k)) (H : TorsSq kdeg (kosD m ev) t) :
    TorsSq kdeg (kosD (fun i j j' => (m i j j').map f) ev') (f t * (((∏ a, c a)⁻¹ : R'ˣ) : R') ^ 2) := by
  have H' := torsSq_diag _ _ (Sum.elim (fun _ => 1) (fun a => (c a)⁻¹)) _ (torsSq_map R _ kdeg _ R' f t H)
  convert H' using 2
  · ext p q
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
    rcases p with p | a <;> rcases q with ⟨I, k⟩ | b
    · simp [kosD, apply_ite f]
    · simp [kosD]
    · by_cases hI : I = ∅
      · subst hI
        have e := hev a k
        simp only [kosD, if_true, Sum.elim_inl, Sum.elim_inr, inv_one, Units.val_one, _root_.mul_one]
        exact ((Units.eq_mul_inv_iff_mul_eq _).2 e).trans (_root_.mul_comm _ _)
      · simp [kosD, hI]
    · simp [kosD]
  · congr 1
    rw [← Finset.prod_subtype (Finset.univ.filter fun p : KIx g d N => Even (kdeg p)) (by simp)
        (fun p => ((Sum.elim (fun _ => 1) (fun a => (c a)⁻¹) p : R'ˣ) : R')),
      ← Finset.prod_subtype (Finset.univ.filter fun p : KIx g d N => ¬ Even (kdeg p)) (by simp)
        (fun p => (((Sum.elim (fun _ => 1) (fun a => (c a)⁻¹) p : R'ˣ)⁻¹ : R'ˣ) : R')),
      Finset.prod_filter, Finset.prod_filter, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, inv_one, Units.val_one, ite_self, Finset.prod_const_one, _root_.one_mul]
    simp [kdeg, ← Finset.prod_inv_distrib]

theorem kaForm_map {R R' : Type} [CommRing R] [CommRing R'] (F : Rˣ →* R'ˣ) (g n l l' : ℕ) (t t' J : Rˣ)
    (lam lam' : ℕ → Rˣ) : F (kaForm g n l l' t t' lam lam' J) =
      kaForm g n l l' (F t) (F t') (fun j => F (lam j)) (fun j => F (lam' j)) (F J) := by
  simp only [kaForm, tComb, map_mul, map_zpow, map_pow, map_prod]

theorem via_mul {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} {l l' k : ℕ}
    (hk : l + l' = k) {a' b' : ∀ i, Γ(Y, L'.U i)} {a b : ∀ j, Γ(X, L.U j)} (ha : KeyVia.Via w l a' a)
    (hb : KeyVia.Via w l' b' b) : KeyVia.Via w k (fun i => a' i * b' i) (fun j => a j * b j) := by
  intro j i h
  rw [map_mul, map_mul, ha j i h, hb j i h, ← hk, pow_add, _root_.mul_mul_mul_comm]

theorem coords_mul {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ w}
    (hx : KeyVia x' x f φ w) {n l k N : ℕ} (hk : n + l = k) {s : RR x n} {s' : RR x' n} {e : RR x l} {e' : RR x' l}
    {b : Fin N → RR x k} {b' : Fin N → RR x' k} {c : Fin N → R} (hs : SecVia x' x φ w s' s)
    (he : SecVia x' x φ w e' e) (hb : ∀ i, SecVia x' x φ w (b' i) (b i))
    (hc : Coords x b c (fun i => (show Γ(x.P.A.left, x.P.L.U i) from s.f i) * (show Γ(x.P.A.left, x.P.L.U i) from e.f i))) :
    Coords x' b' (fun i => f (c i))
      (fun i => (show Γ(x'.P.A.left, x'.P.L.U i) from s'.f i) * (show Γ(x'.P.A.left, x'.P.L.U i) from e'.f i)) := by
  obtain ⟨-, -, -, ⟨hP, -⟩, -⟩ := hx
  have H := KeyVia.Via.comb (w := w) (l := k) (b' := fun i => (b' i).f) (b := fun i => (b i).f) f x.P.A.hom
    x'.P.A.hom hP.w hb c
  have H' := via_mul (w := w) hk (a' := s'.f) (b' := e'.f) (a := s.f) (b := e.f) hs he
  have H'' := (congrArg (KeyVia.Via w k _) (funext hc)).mp H'
  exact fun i => congrFun (KeyVia.Via.unique x.P.isLB H'' H) i

theorem kaVal_baseChange : Out.Laws → ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (κ : Rˣ), admitted x.P.g n l l' al → KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → KaVal x n l l' al s κ → KaVal x' n l l' al s' (Units.map f.toMonoidHom κ) := by
  intro laws R R' _ _ _ _ _ x x' f φ w n l l' al hg s s' κ hadm hx hs hκ
  obtain ⟨⟨A', ab, g', sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := x'
  obtain rfl : g' = x.P.g := hg
  let x' : KeyIn R' := ⟨⟨A', ab, x.P.g, sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩
  obtain ⟨z, ch, b, b₂, t, t₂, J, lam, lam₂, hz, hJ, hb, hb₂, ht, ht₂, rfl⟩ := hκ
  obtain ⟨z', ch', u, hz', hjac, hval⟩ := etZ_baseChange R R' x x' f φ w n _ rfl s s' z ch hx hs hz
  have hex := ((KeyVia.main R R' x x' f).2 φ w hx).1
  have key : ∀ (l : ℕ) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (lam : ℕ → Rˣ) (t : Rˣ),
      x.P.g * n < l →
      (∀ j ≤ x.P.g, IsBasis x (b j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b j) (lam j)) → KosVal x l s z ch b t →
      ∃ b' : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x' (l - j * n),
        (∀ j ≤ x.P.g, IsBasis x' (b' j) ∧
          IsSquareDeterminantComparison x' (l - j * n) (al (l - j * n)) (b' j) (Units.map f.toMonoidHom (lam j))) ∧
        KosVal x' l s' z' ch' b' (Units.map f.toMonoidHom t * (∏ a, u a) ^ (-2 * (l : ℤ)) : R'ˣ) := by
    intro l b lam t hl hb ⟨m, hm, ht⟩
    choose b' hb' using fun j k => (hex _ (b j k)).exists
    refine ⟨b', fun j hj => ⟨?_, ?_⟩, fun i j j' => (m i j j').map f, fun i j hj k => ?_, ?_⟩
    · have h₁ : j * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
      exact (GlobalTheory.KeyBasis.main laws R x (l - j * n) (by omega)).2 (b j) (hb j hj).1 R' f x' φ w (b' j) hx (hb' j)
    · exact GlobalTheory.SimilBaseChange.cmpVal_baseChange_similitude R R' x x' f φ w _ _ rfl (b j) (b' j) (lam j) (hadm.2.2.2 _) hx (hb' j) (hb j hj).2
    · have h₁ : (j + 1) * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
      have h₂ : n + (l - (j + 1) * n) = l - j * n := by
        rw [Nat.add_mul, Nat.one_mul] at h₁ ⊢
        omega
      exact coords_mul hx h₂ (hs i) (hb' (j + 1) k) (hb' j) (hm i j hj k)
    · have H := torsSq_kosD_map f m
        (fun j => Matrix.of fun a k => valT (T := R) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))
        (fun j => Matrix.of fun a k => valT (T := R') (z' a).left (x'.P.L.U (ch' a)) ((b' j k).f (ch' a)))
        (fun a => u a ^ (l - 0 * n)) t
        (fun a k => (congrArg _ (Units.val_pow_eq_pow_val _ _)).trans (hval _ (b 0 k) (b' 0 k) a (hb' 0 k))) ht
      have e : (∏ a, u a) ^ (-2 * (l : ℤ)) = (∏ a, u a ^ (l - 0 * n))⁻¹ ^ 2 := by
        rw [Finset.prod_pow, Nat.zero_mul, Nat.sub_zero]
        group
      rw [e]
      exact H
  obtain ⟨c, hc, hct⟩ := key l b lam t hadm.2.1 hb ht
  obtain ⟨c₂, hc₂, hct₂⟩ := key l' b₂ lam₂ t₂ (hadm.2.1.trans hadm.2.2.1) hb₂ ht₂
  refine ⟨z', ch', c, c₂, _, _, Units.map f.toMonoidHom J * (∏ a, u a) ^ (-((x.P.g * n : ℕ) : ℤ)), _, _,
    hz', ?_, hc, hc₂, hct, hct₂, ?_⟩
  · rw [zpow_neg, zpow_natCast, Units.val_mul, eq_comm, Units.eq_mul_inv_iff_mul_eq, Units.val_pow_eq_pow_val,
      Units.coe_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine (Finset.prod_congr rfl fun a _ => hjac a).trans ?_
    rw [← map_prod, ← hJ]
    rfl
  · have H := kaForm_homogeneous R' x.P.g n l l' (Units.map f.toMonoidHom t) (Units.map f.toMonoidHom t₂)
      (Units.map f.toMonoidHom J) (∏ a, u a) 1 1 (fun j => Units.map f.toMonoidHom (lam j))
      (fun j => Units.map f.toMonoidHom (lam₂ j)) (fun _ => 1) (fun _ => 1) hadm.2.1 hadm.2.2.1
    simp only [one_zpow, one_pow, _root_.mul_one, Finset.prod_const_one] at H
    exact (kaForm_map _ _ _ _ _ _ _ _ _ _).trans H.symm

end GlobalTheory.KaBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LiftIdempotentEqOfSameComplexComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem isPreirreducible_connectedComponent_of_smooth {K : Type} [Field K] {Z : Scheme.{0}}
    (g : Z ⟶ Spec (.of K)) [Smooth g] (z : Z) : IsPreirreducible (connectedComponent z) := by
  have hK : GlobalTheory.IsNormalScheme (Spec (.of K)) := inferInstance
  have : GlobalTheory.IsNormalScheme Z := (GlobalTheory.isNormalScheme_iff Z).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g ((GlobalTheory.isNormalScheme_iff _).mp hK))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  rw [GlobalTheory.IsNormalScheme.connectedComponent_eq_irreducibleComponent]
  exact isIrreducible_irreducibleComponent.2

theorem apply_eq_of_isPreirreducible {T F : Type} [CommRing T] [Field F] (f g : T →+* F)
    (C : Set (PrimeSpectrum T)) (hC : IsPreirreducible C) (z : PrimeSpectrum F)
    (hf : PrimeSpectrum.comap f z ∈ C) (hg : PrimeSpectrum.comap g z ∈ C)
    (e : T) (he : IsIdempotentElem e) : f e = g e := by
  have hz : ∀ a : F, a ∈ z.asIdeal ↔ a = 0 := by
    intro a
    have : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right z.2.ne_top
    rw [this, Ideal.mem_bot]
  have key : ∀ (f g : T →+* F), PrimeSpectrum.comap f z ∈ C → PrimeSpectrum.comap g z ∈ C →
      f e = 0 → g e = 1 → False := by
    intro f g hf hg h0 h1
    obtain ⟨x, -, hx1, hx2⟩ := hC (PrimeSpectrum.basicOpen (1 - e)) (PrimeSpectrum.basicOpen e)
      (PrimeSpectrum.basicOpen _).2 (PrimeSpectrum.basicOpen _).2
      ⟨_, hf, by simp [hz, h0]⟩ ⟨_, hg, by simp [hz, h1]⟩
    have h : (1 - e) * e ∈ x.asIdeal := by
      rw [sub_mul, _root_.one_mul, he.eq, sub_self]; exact x.asIdeal.zero_mem
    exact (x.2.mem_or_mem h).elim hx1 hx2
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map f) with h | h <;>
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map g) with h' | h'
  · rw [h, h']
  · exact (key f g hf hg h h').elim
  · exact (key g f hg hf h' h).elim
  · rw [h, h']

theorem lift_eq_of_sameComp_of_isIdempotentElem :
    ∀ (K : Type) [Field K] [Algebra K ℂ] (X : Scheme.{0}) (s : X ⟶ Sp K) (R : Type) [CommRing R] [Algebra K R] (i : Sp R ⟶ X) (p q : R →ₐ[K] ℂ), Smooth s → IsOpenImmersion i → i ≫ s = spMap (algebraMap K R) → SameComp s (algebraMap K ℂ) (spMap p.toRingHom ≫ i) (spMap q.toRingHom ≫ i) → ∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) q (fun _ _ => Commute.all _ _) e := by
  intro K _ _ X s R _ _ i p q hs hi his ⟨hp, hq, hpq⟩ e he
  let T := ℂ ⊗[K] R
  let j : Sp T ⟶ pullback s (spMap (algebraMap K ℂ)) :=
    (pullbackSpecIso K ℂ R).inv ≫ (pullbackSymmetry _ _).hom ≫
    pullback.map (spMap (algebraMap K R)) (spMap (algebraMap K ℂ)) s (spMap (algebraMap K ℂ)) i (𝟙 _) (𝟙 _)
      (by rw [his, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  haveI : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  let iL : ℂ →+* T := Algebra.TensorProduct.includeLeftRingHom
  let iR : R →+* T := (Algebra.TensorProduct.includeRight (R := K) (A := ℂ) (B := R) : R →+* T)
  have hj1 : j ≫ pullback.fst _ _ = spMap iR ≫ i := by
    simp only [j, Category.assoc, pullback.lift_fst]
    rw [pullbackSymmetry_hom_comp_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  have hj2 : j ≫ pullback.snd _ _ = spMap iL := by
    simp only [j, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst]
  have hl : ∀ (r : R →ₐ[K] ℂ) (hr : (spMap r.toRingHom ≫ i) ≫ s = 𝟙 _ ≫ spMap (algebraMap K ℂ)),
      pullback.lift (spMap r.toRingHom ≫ i) (𝟙 _) hr =
        spMap (Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) r (fun _ _ => Commute.all _ _)).toRingHom ≫ j := by
    intro r hr
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hj1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      ext x
      change r x = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) r (fun _ _ => Commute.all _ _) (1 ⊗ₜ[K] x)
      rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    · rw [pullback.lift_snd, Category.assoc, hj2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
      congr 1
      ext x
      change (x : ℂ) = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) r (fun _ _ => Commute.all _ _) ((x : ℂ) ⊗ₜ[K] 1)
      rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      rfl
  let z : PrimeSpectrum ℂ := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 := hpq z
  have hC := isPreirreducible_connectedComponent_of_smooth (pullback.snd s (spMap (algebraMap K ℂ)))
    (pullback.lift (spMap q.toRingHom ≫ i) (𝟙 _) hq z)
  have h2 := mem_connectedComponent (x := pullback.lift (spMap q.toRingHom ≫ i) (𝟙 _) hq z)
  generalize connectedComponent (pullback.lift (spMap q.toRingHom ≫ i) (𝟙 _) hq z) = C at h1 h2 hC
  rw [hl] at h1 h2
  exact apply_eq_of_isPreirreducible _ _ (j ⁻¹' C) (hC.preimage j.isOpenEmbedding) z h1 h2 e he

end GlobalTheory.KeyFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SameCompOfIsHolTo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem sameComp_of_isHolTo : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsPreconnected B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ∀ b ∈ B, ∀ b' ∈ B, SameComp s σ (y b) (y b') := by
  intro K _ σ X s m B y hB hc hs hy b hb b' hb'
  classical
  have hs' : ∀ w ∈ B, y w ≫ s = 𝟙 _ ≫ spMap σ := fun w hw => by rw [Category.id_comp]; exact hs w hw
  let c : (Fin m → ℂ) → (Sp ℂ ⟶ pullback s (spMap σ)) := fun w =>
    if h : w ∈ B then pullback.lift (y w) (𝟙 _) (hs' w h) else pullback.lift (y b) (𝟙 _) (hs' b hb)
  have hcw : ∀ w (h : w ∈ B), c w = pullback.lift (y w) (𝟙 _) (hs' w h) := fun w h => dif_pos h
  have h1 : ∀ w ∈ B, c w ≫ pullback.fst s (spMap σ) = y w := fun w h => by rw [hcw w h, pullback.lift_fst]
  have h2 : ∀ w, c w ≫ pullback.snd s (spMap σ) = 𝟙 _ := fun w => by
    by_cases h : w ∈ B
    · rw [hcw w h, pullback.lift_snd]
    · rw [show c w = pullback.lift (y b) (𝟙 _) (hs' b hb) from dif_neg h, pullback.lift_snd]
  have hopen : ∀ U : (pullback s (spMap σ)).Opens, IsOpen {w | w ∈ B ∧ ⊤ ≤ c w ⁻¹ᵁ U} := fun U => by
    refine (GlobalTheory.holFamily_of_isPullback GlobalTheory.valAt'_rules B (IsPullback.of_hasPullback s (spMap σ)) c
      (fun U f => ?_) (fun U f => ?_) U 0).1
    · have e : {w | w ∈ B ∧ ⊤ ≤ (c w ≫ pullback.fst s (spMap σ)) ⁻¹ᵁ U} = {w | w ∈ B ∧ ⊤ ≤ y w ⁻¹ᵁ U} := by
        ext w
        simp only [Set.mem_setOf_eq]
        exact and_congr_right fun h => by rw [h1 w h]
      rw [e]
      exact ⟨(hy U f).1, (hy U f).2.congr fun w hw => by rw [h1 w hw.1]⟩
    · simp only [h2]
      refine ⟨?_, differentiableOn_const _⟩
      by_cases h : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U
      · simpa only [h, and_true, Set.setOf_mem_eq] using hB
      · simp only [h, and_false, Set.setOf_false, isOpen_empty]
  have hcont : ContinuousOn (fun w => c w (default : PrimeSpectrum ℂ)) B := by
    rw [continuousOn_open_iff hB]
    intro t ht
    convert hopen ⟨t, ht⟩ using 1
    ext w
    simp only [Set.mem_setOf_eq, GlobalTheory.top_le_preimage_iff_mem]
    rfl
  refine ⟨hs' b hb, hs' b' hb', fun z => ?_⟩
  obtain rfl : z = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  rw [← hcw b hb, ← hcw b' hb']
  exact (hc.image _ hcont).subset_connectedComponent ⟨b', hb', rfl⟩ ⟨b, hb, rfl⟩

end GlobalTheory.KeyFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SqOfCalculus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam
open GlobalTheory.ZM.SiegPull

theorem LamIs.comp {S S' S'' : Scheme.{0}} {A' : Over S''} [GrpObj A'] {A : Over S'} [GrpObj A] {B : Over S}
    {L' : LB A'.left} {L : LB A.left} {Pb : LB (B ⊗ B).left} {ψ : A'.left ⟶ A.left} {φ : A.left ⟶ B.left}
    (hL' : L'.IsLB) (hL : L.IsLB) (hP : Pb.IsLB) (h' : LamIs A' L' A (abelian₂ A L) ψ) (h : LamIs A L B Pb φ) :
    LamIs A' L' B Pb (ψ ≫ φ) := by
  obtain ⟨ψ₂, sψ, iψ⟩ := h'
  obtain ⟨φ₂, sφ, iφ⟩ := h
  exact ⟨ψ₂ ≫ φ₂, isSquare_comp sψ sφ, LBIso.trans (DVR.linComb_isLB _ hL' _ _)
    (pull_isLB (DVR.linComb_isLB _ hL _ _) _) (pull_isLB hP _) iψ (lbIso_pull_comp iφ ψ₂)⟩

theorem PolPB.lamIs {S S' : Scheme.{0}} {P' : Out.PolAV S'} {P : Out.PolAV S} {f : S' ⟶ S}
    {φ : P'.A.left ⟶ P.A.left} (h : PolPB P' P f φ) : LamIs P'.A P'.L P.A (abelian₂ P.A P.L) φ := by
  letI := P.isAb.comm
  letI := P'.isAb.comm
  obtain ⟨φ₂, s⟩ := exists_isSquare h.1.1.w
  exact ⟨φ₂, s, lbIso_lam_pull h.1 h.2.2 s⟩

theorem sqOf_calculus : ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k ζ s) (f : S' ⟶ S), (∀ (g : S'' ⟶ S') (P : Out.PolAV S') (P' : Out.PolAV S'') (φ : P.A.left ⟶ c.A.left) (ψ : P'.A.left ⟶ P.A.left), SqOf P c f φ → PolPB P' P g ψ → SqOf P' c (g ≫ f) (ψ ≫ φ)) ∧ (∀ (P P' : Out.PolAV S') (φ : P.A.left ⟶ c.A.left) (φ' : P'.A.left ⟶ c.A.left), SqOf P c f φ → SqOf P' c f φ' → ∃ e : P'.A ≅ P.A, IsMonHom e.hom ∧ e.hom.left ≫ φ = φ' ∧ LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left) ∧ ∀ (P P' : Out.PolAV S') (φ : P.A.left ⟶ c.A.left) (e : P'.A ≅ P.A), IsMonHom e.hom → P'.g = P.g → LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left → SqOf P c f φ → SqOf P' c f (e.hom.left ≫ φ) := by
  intro h k o _ ζ S S' S'' s c f
  refine ⟨fun g P P' φ ψ H H' => ⟨H'.1.comp H.1, H'.2.1.trans H.2.1,
      LamIs.comp P'.isLB P.isLB c.isLB H'.lamIs H.2.2⟩, fun P P' φ φ' H H' => ?_,
    fun P P' φ e he hg hl H => ⟨((isGrpPullback_of_iso e).comp H.1).congr (Category.id_comp _) rfl,
      hg.trans H.2.1, LamIs.comp P'.isLB P.isLB c.isLB hl H.2.2⟩⟩
  obtain ⟨e, he, hφ⟩ := grpPullback_iso H'.1 H.1
  obtain ⟨φ₂, s₂, i₂⟩ := H.2.2
  obtain ⟨φ₂', s₂', i₂'⟩ := H'.2.2
  refine ⟨e, he, hφ, _, isSquare_tensor e.hom, ?_⟩
  have k₁ := lbIso_pull_comp i₂ (e.hom ⊗ₘ e.hom).left
  rw [isSquare_unique (isSquare_comp (isSquare_tensor e.hom) s₂) s₂' hφ] at k₁
  exact LBIso.trans (DVR.linComb_isLB _ P'.isLB _ _) (pull_isLB c.isLB _)
    (pull_isLB (DVR.linComb_isLB _ P.isLB _ _) _) i₂' k₁.symm

end GlobalTheory.KeyFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueKnownOfPolarizedPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.KnownScale

theorem val_scale {P : Out.PolAV (Sp ℂ)} {hg rig hr th hth v hv th' hth' v' hv'} {a : ℂ} (ha : a ≠ 0)
    {N : Matrix (Fin P.g) (Fin P.g) ℂ} (h₁ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i)
    (h₂ : ∀ i, IsLieComb (N i) v (v' i)) {t : ℂ} (h : Val ⟨P, hg, rig, hr, th, hth, v, hv⟩ t) :
    Val ⟨P, hg, rig, hr, th', hth', v', hv'⟩ (N.det ^ 4 / a ^ 8 * t) := by
  obtain ⟨τ, M, p, q, c, hpq, hc, ⟨u, k₁, k₂, k₃, k₄, k₅, k₆⟩, rfl⟩ := h
  have := P.isAb.comm
  refine ⟨τ, N * M, p, q, a * c, hpq, mul_ne_zero ha hc, ⟨u, k₁, k₂, k₃, k₄, fun i z hz => ?_, fun i => ?_⟩, ?_⟩
  · refine ((congrArg (valAt' _ _) (h₁ i)).trans (valAt'_mul _ _ _ _)).trans ?_
    rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
    refine (congrArg (a * ·) (k₅ i z hz)).trans ?_
    simp only [_root_.mul_assoc]
  · have k := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 k₆ (h₂ i)
    have e : ∑ j, N i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • (N * M) i := by
      simp only [smul_comm (N i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
      rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum]
      rfl
    rwa [e] at k
  · rw [Matrix.det_mul, mul_pow, mul_pow, div_mul_div_comm]

theorem det_map_cast {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') {m n : ℕ} (e : m = n)
    (M : Matrix (Fin n) (Fin n) K) :
    (Matrix.of fun i j : Fin m => f (M (i.cast e) (j.cast e))).det = f M.det := by
  subst e
  exact (f.map_det M).symm

theorem known_change {K : Type} [Field K] {P : Out.PolAV (Sp K)} {hg rig hr th hth v hv th' hth' v' hv'} (a : Kˣ)
    (h₁ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ (a : K) * LB.Sec.f th i)
    (h : Known K ⟨P, hg, rig, hr, th, hth, v, hv⟩) : Known K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ := by
  obtain ⟨t₀, ht₀⟩ := h
  have := P.isAb.comm
  choose N hN using fun i => (hv'.2 (v i) (hv.1 i)).exists
  have hdet : IsUnit (Matrix.of N).det :=
    ((GlobalTheory.LieComb.lieComb_algebra K P.A P.g v' hv'.1).2.2.2.2 (Matrix.of N) v hv' hN).1 hv
  have h₁' : ∀ i, LB.Sec.f th i = constFn P.A.hom _ ((a⁻¹ : Kˣ) : K) * LB.Sec.f th' i := fun i => by
    rw [h₁, ← _root_.mul_assoc, ← KeyPow.constFn_mul, Units.inv_mul, KeyPow.constFn_one, _root_.one_mul]
  refine ⟨((Matrix.of N).det)⁻¹ ^ 4 / (a : K) ^ 8 * t₀, fun e x hx => ?_⟩
  obtain ⟨Q, hgQ, rigQ, hrQ, s, hs, u, hu⟩ := x
  obtain ⟨eg⟩ : Nonempty (Q.g = P.g) := by
    obtain ⟨_, _, _, hg, _⟩ := hx
    exact ⟨hg⟩
  have := Q.isAb.comm
  obtain ⟨ex, -, comp, sgl, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ Q.A Q.g u hu.1
  let N' : Matrix (Fin Q.g) (Fin Q.g) ℂ := Matrix.of fun i j => e (Matrix.of N (i.cast eg) (j.cast eg))
  have hd : N'.det = e (Matrix.of N).det := det_map_cast e eg (Matrix.of N)
  choose u₀ hu₀ using fun i => (ex (N' i)).exists
  have hb₀ : IsLieBasis u₀ := (bas N' u₀ hu hu₀).2 (hd ▸ hdet.map e)
  choose M hM using fun i => (hb₀.2 (u i) (hu.1 i)).exists
  have hMN : Matrix.of M * N' = 1 := by
    funext i
    have k := (hu.2 (u i) (hu.1 i)).unique (comp _ (fun j => N' j) u₀ (M i) (u i) hu₀ (hM i)) (sgl i)
    rw [← Matrix.vecMul_eq_sum] at k
    refine k.trans ?_
    simpa using (smul_one_row (1 : ℂ) i).symm
  have hMd : (Matrix.of M).det = (e (Matrix.of N).det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hd, ← Matrix.det_mul, hMN, Matrix.det_one]
  obtain ⟨s₀, e₀, e₁, hle⟩ := exists_sec_div Q.A.hom (a := e a) (b := e ((a⁻¹ : Kˣ) : K))
    (by rw [← map_mul, Units.mul_inv, map_one]) s
  have hs₀ : ∀ p : Sp ℂ, ∃ z : Q.A.left, Q.A.hom z = p ∧ z ∈ Out.nonzeroLocus s₀ :=
    fun p => (hs p).imp fun z hz => ⟨hz.1, hle hz.2⟩
  have hx₀ := KeyPBScale.keyPB_scale K ℂ e P hg rig hr th' hth' v' hv' th hth v hv _ (Matrix.of N) Q eg hgQ rigQ hrQ
    s hs u hu s₀ hs₀ u₀ hb₀ h₁' hN e₀ hu₀ hx
  have k := val_scale (hth' := hs) (hv' := hu) (N := Matrix.of M) ((map_ne_zero e).2 a.ne_zero) e₁ hM (ht₀ e _ hx₀)
  rw [hMd] at k
  rwa [map_mul, map_div₀, map_pow, map_pow, map_inv₀]

theorem known_of_keyPB {K : Type} [Field K] {y y' : KeyIn K} (h : KeyPB y' y (RingHom.id K)) (hy : Known K y) :
    Known K y' :=
  hy.imp fun _ ht e x hx => ht e x (keyPB_trans _ _ _ y y' x (RingHom.id K) e h hx)

theorem known_of_polPB : Out.Laws → ∀ (K : Type) [Field K] (y y' : KeyIn K) (φ : y'.P.A.left ⟶ y.P.A.left), PolPB y'.P y.P (𝟙 _) φ → Known K y → Known K y' := by
  intro hL K _ y y' φ ⟨h₁, h₂, h₃⟩ hy
  have e : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
  obtain ⟨rig, hr, th, hth, v, hv, hz⟩ := KeyTf.exists_keyPB_on K K (RingHom.id K) y y'.P φ y'.g_pos h₂ (e ▸ h₁) h₃
  obtain ⟨a, t, ht, hta, hid⟩ := (KeyOnPol.main hL K).2 ⟨y'.P, y'.g_pos, rig, hr, th, hth, v, hv⟩
    y'.rig y'.rig_gen y'.th y'.th_ne y'.v y'.basis
  exact known_of_keyPB hid (known_change a hta (known_of_keyPB hz hy))

end GlobalTheory.KnownScale
end
end

