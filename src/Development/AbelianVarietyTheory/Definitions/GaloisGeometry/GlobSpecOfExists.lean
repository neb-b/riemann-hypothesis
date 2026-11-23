module

public import Mathlib
public import Formalism.SharpRestriction.GrowthBounds.DataGChain
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.LocalToGlobal.Columns.Bundle0004

@[expose] public section

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]

structure PlTie (X : Fields) (P : Places p O Kf) where
  pr : Fin P.nV → HeightOneSpectrum (𝓞 X.E)
  iw : ∀ v, X.E →+* P.Qq v
  eK : X.K →+* Kf
  pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ X.Tau
  pr_inj : Function.Injective pr
  pr_ne : ∀ v v', pr v ≠ conjPrime₂ (pr v')
  pr_all : ∀ Q : HeightOneSpectrum (𝓞 X.E), ((p : ℕ) : 𝓞 X.E) ∈ Q.asIdeal ↔ ∃ v, Q = pr v ∨ Q = conjPrime₂ (pr v)
  iw_int : ∀ v x, IntAt (pr v) x ↔ iw v x ∈ Set.range (algebraMap (P.W v) (P.Qq v))
  iw_dense : ∀ v (y : P.W v) (n : ℕ), ∃ (x : 𝓞 X.E) (z : P.W v),
    iw v (x : X.E) = algebraMap (P.W v) (P.Qq v) (y + (p : P.W v) ^ n * z)
  even : ∀ v (s : Fin (P.n' v)), Even s.val → ∀ x, eK (X.emb (pos ⟨v, s⟩) x) = P.ι v ((P.σ v ^ s.val) (iw v x))
  odd : ∀ v (s : Fin (P.n' v)), ¬ Even s.val → ∀ x, eK (X.embBar (pos ⟨v, s⟩) x) = P.ι v ((P.σ v ^ s.val) (iw v x))

def SameOff {E : Type} [Field E] [NumberField E] {n : ℕ} (p : ℕ) (N N' : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ Q : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal → localization₂ Q.asIdeal N = localization₂ Q.asIdeal N'

structure PSys (X : Fields) (n p : ℕ) (lam : X.Tau → DomWeight n) (S : GSD X.K) where
  u : S.G →* UF X.E n
  chr : S.G →* X.Kˣ
  eV : S.V ≃ₗ[X.K] VV X.K lam
  N : S.D → Submodule (𝓞 X.E) (Sp X.E n)

  Aw : S.D → S.D → Prop
  aw_equiv : Equivalence Aw
  aw_smul : ∀ (g : S.G) d d', Aw d d' → Aw (g • d) (g • d')
  aw_off : ∀ d d', Aw d d' → SameOff p (N d) (N d')
  aw_ex : ∀ d N', Submodule.IsLattice X.E N' → IsUnimodular (hStd X.E n) N' → SameOff p (N d) N' → ∃! d', Aw d d' ∧ N d' = N'
  lat : ∀ d, Submodule.IsLattice X.E (N d)
  uni : ∀ d, IsUnimodular (hStd X.E n) (N d)
  N_smul : ∀ (g : S.G) d, N (g • d) = gmap (u g).1 (N d)
  chr_root : ∀ g, ∃ k : ℕ, 0 < k ∧ chr g ^ k = 1
  rho : ∀ g x, eV (S.ρ g x) = ((chr g : X.Kˣ) : X.K) • rhoVr X.emb lam (ufGL X.E n (u g)) (eV x)
  del : ∀ d (w : HeightOneSpectrum (𝓞 X.K)), ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal → ∀ x,
    x ∈ localization₂ w.asIdeal (S.Del d) ↔ eV x ∈ localization₂ w.asIdeal (delAtr X.emb lam (N d))
  nab : ∀ d (w : HeightOneSpectrum (𝓞 X.K)), ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal → ∀ x,
    x ∈ localization₂ w.asIdeal (S.Nab d) ↔ eV x ∈ localization₂ w.asIdeal (nabAtr X.emb lam (N d))

section Loc

variable {X : Fields} {P : Places p O Kf} (T : PlTie X P) {n : ℕ} (hn : n = P.m + 1)

def PlTie.vec (v : Fin P.nV) (x : Sp X.E n) : Fin (P.m + 1) → P.Qq v := fun i => T.iw v (x (Fin.cast hn.symm i))

def PlTie.act (v : Fin P.nV) : UF X.E n →* GL (Fin (P.m + 1)) (P.Qq v) :=
  (Formalism.UG.bc (T.iw v)).comp
    ((Units.map (Matrix.reindexAlgEquiv X.E X.E (finCongr hn)).toMulEquiv.toMonoidHom).comp (ufGL X.E n))

def PlTie.detTw (c : ℤ) (γ : UF X.E n) : Kf :=
  (∏ τ, T.eK (X.emb τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E))) ^ c

def PlTie.WtEq (lam : X.Tau → DomWeight n) (c : ℤ) : Prop :=
  ∀ v s i, P.lam0 v s i = (lam (T.pos ⟨v, s⟩)).w (Fin.cast hn.symm i) + c

end Loc

namespace RetractionModules

variable {X : Fields} {n : ℕ}

theorem star_det_mul {E : Type} [Field E] [StarRing E] (γ : UF E n) :
    star ((LinearEquiv.det γ.1 : Eˣ) : E) * ((LinearEquiv.det γ.1 : Eˣ) : E) = 1 := by
  set M : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' (γ.1 : Sp E n →ₗ[E] Sp E n) with hM
  have hd : ((LinearEquiv.det γ.1 : Eˣ) : E) = M.det := by
    rw [LinearEquiv.coe_det, hM, LinearMap.det_toMatrix']
  have hu : M.conjTranspose * M = 1 := by
    ext i j
    have h := γ.2 (Pi.single i 1) (Pi.single j 1)
    simp only [hStd, LinearMap.mk₂'ₛₗ_apply] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, hM, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    refine h.trans ?_
    rw [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp [Pi.single_apply]
    · simp [Pi.single_apply, hij, Ne.symm hij]
  rw [hd, ← Matrix.det_conjTranspose, ← Matrix.det_mul, hu, Matrix.det_one]

variable {P : Places p O Kf}

theorem sigma_pow_mem (v : Fin P.nV) (s : ℕ) (x : P.W v) :
    ∃ y : P.W v, (P.σ v ^ s) (algebraMap (P.W v) (P.Qq v) x) = algebraMap (P.W v) (P.Qq v) y := by
  induction s with
  | zero => exact ⟨x, rfl⟩
  | succ s ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨z, hz⟩ := (P.setting v).frob y
    refine ⟨y ^ p + (p : P.W v) * z, ?_⟩
    rw [pow_succ']
    change P.σ v ((P.σ v ^ s) _) = _
    rw [hy, hz]

theorem prod_mem (T : PlTie X P) {δ : X.E} (hδ : star δ * δ = 1) :
    (∏ τ, T.eK (X.emb τ δ)) ∈ (algebraMap O Kf).range := by
  rw [← Equiv.prod_comp T.pos, Fintype.prod_sigma]
  refine Subring.prod_mem _ fun v _ => ?_
  have hS := P.setting v
  haveI := hS.frac_alt
  haveI := hS.frac_O
  have hδ0 : δ ≠ 0 := by rintro rfl; simp at hδ
  have hst : star δ⁻¹ = δ := by
    rw [star_inv₀]; exact (eq_inv_of_mul_eq_one_right hδ).symm
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := P.Qq v) hS.p_unif
    ((map_ne_zero (T.iw v)).2 hδ0)
  have hp0 : (p : Kf) ≠ 0 := by
    have h1 : algebraMap (P.W v) (P.Qq v) (p : P.W v) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hS.p_unif.ne_zero
    have h2 := (map_ne_zero (P.ι v)).2 h1
    simpa using h2
  have key : ∀ s : Fin (P.n' v), ∃ t : O, T.eK (X.emb (T.pos ⟨v, s⟩) δ) =
      algebraMap O Kf t * (p : Kf) ^ (a * (-1) ^ s.val) := by
    intro s
    by_cases hs : Even s.val
    · obtain ⟨y, hy⟩ := sigma_pow_mem v s.val (u : P.W v)
      refine ⟨P.j v y, ?_⟩
      rw [T.even v s hs, hu, Units.smul_def, Algebra.smul_def, map_mul, map_mul, hy, hS.ι_comp, hs.neg_one_pow]
      simp
    · obtain ⟨y, hy⟩ := sigma_pow_mem v s.val ((u⁻¹ : (P.W v)ˣ) : P.W v)
      refine ⟨P.j v y, ?_⟩
      have h1 := T.odd v s hs δ⁻¹
      have h2 : X.embBar (T.pos ⟨v, s⟩) δ⁻¹ = X.emb (T.pos ⟨v, s⟩) δ := by
        simp only [Fields.embBar, RingHom.comp_apply, starRingEnd_apply, hst]
      rw [h2] at h1
      rw [h1, map_inv₀, hu, Units.smul_def, Algebra.smul_def, mul_inv, ← map_units_inv, map_mul, map_mul, hy, hS.ι_comp,
        (Nat.not_even_iff_odd.1 hs).neg_one_pow]
      simp
  choose t ht using key
  rw [Finset.prod_congr rfl fun s _ => ht s, Finset.prod_mul_distrib, ← map_prod]
  have hsum : ∑ s : Fin (P.n' v), (a * (-1) ^ s.val : ℤ) = 0 := by
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i), neg_one_geom_sum, if_pos hS.even, mul_zero]
  have hprod : ∀ (S : Finset (Fin (P.n' v))), ∏ s ∈ S, (p : Kf) ^ (a * (-1) ^ s.val : ℤ) =
      (p : Kf) ^ (∑ s ∈ S, (a * (-1) ^ s.val : ℤ)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert s S hs ih => rw [Finset.prod_insert hs, Finset.sum_insert hs, zpow_add₀ hp0, ih]
  rw [hprod, hsum, zpow_zero, mul_one]
  exact ⟨_, rfl⟩

theorem detTw_mem (T : PlTie X P) (c : ℤ) (γ : UF X.E n) : T.detTw c γ ∈ (algebraMap O Kf).range := by
  have h := star_det_mul γ
  have h1 := prod_mem T h
  set δ := ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)
  have h' : star δ⁻¹ * δ⁻¹ = 1 := by rw [star_inv₀, ← mul_inv, h, inv_one]
  have h2 := prod_mem T h'
  simp only [map_inv₀, Finset.prod_inv_distrib] at h2
  unfold PlTie.detTw
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · rw [zpow_natCast]; exact Subring.pow_mem _ h1 k
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact Subring.pow_mem _ h2 k

theorem nV_pos (T : PlTie X P) (hp : p.Prime) : 0 < P.nV := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 X.E) := by
    intro h
    have h1 := h.map (Algebra.norm ℤ)
    have h2 : Algebra.norm ℤ ((p : ℕ) : 𝓞 X.E) = (p : ℤ) ^ Module.finrank ℤ (𝓞 X.E) := by
      have := Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 X.E) (p : ℤ)
      simpa using this
    rw [h2, isUnit_pow_iff Module.finrank_pos.ne', Int.ofNat_isUnit] at h1
    exact hp.not_isUnit h1
  have hp0 : ((p : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨M, hM, hpM⟩ := exists_max_ideal_of_mem_nonunits hnu
  obtain ⟨v, -⟩ := (T.pr_all ⟨M, hM.isPrime, fun h => hp0 (by simpa [h] using hpM)⟩).1 hpM
  exact v.pos

end RetractionModules

theorem PlTie.nV_pos_of_prime {X : Fields} {P : Places p O Kf} (T : PlTie X P) (hp : p.Prime) : 0 < P.nV :=
  RetractionModules.nV_pos T hp

namespace PSys

variable {X : Fields} {n : ℕ} {lam : X.Tau → DomWeight n} {S : GSD X.K} (Y : PSys X n p lam S)

def Comp : Type := Quot fun d d' : S.D => ∃ g : S.G, Y.Aw (g • d) d'

def rep (a : Y.Comp) : S.D := Quot.out a

def Gam (d : S.D) : Subgroup S.G where
  carrier := {g | Y.Aw (g • d) d}
  one_mem' := by
    show Y.Aw ((1 : S.G) • d) d
    rw [one_smul]; exact Y.aw_equiv.refl d
  mul_mem' := by
    intro a b ha hb
    show Y.Aw ((a * b) • d) d
    rw [mul_smul]
    exact Y.aw_equiv.trans (Y.aw_smul a _ _ hb) ha
  inv_mem' := by
    intro a ha
    have h := Y.aw_smul a⁻¹ _ _ (show Y.Aw (a • d) d from ha)
    rw [inv_smul_smul] at h
    exact Y.aw_equiv.symm h

theorem finite_comp (h : S.Ok) : Finite Y.Comp := by
  have := h.fin_orb
  refine Finite.of_surjective (fun c : S.Cl => (Quot.mk _ (S.outSec.rep c) : Y.Comp)) ?_
  rintro ⟨d⟩
  refine ⟨S.cls d, Quot.sound ⟨S.outSec.mv d, ?_⟩⟩
  rw [S.outSec.mv_smul]
  exact Y.aw_equiv.refl d

variable {P : Places p O Kf} (T : PlTie X P) (hn : n = P.m + 1)

structure ChiLift (c : ℤ) where
  χ : ∀ d : S.D, Y.Gam d →* Oˣ
  spec : ∀ d (g : Y.Gam d), algebraMap O Kf (χ d g : O) = T.eK ((Y.chr g.1 : X.Kˣ) : X.K) * T.detTw c (Y.u g.1)

theorem exists_chi (hp : p.Prime) (c : ℤ) : ∃ χ : S.G →* Oˣ,
    ∀ g, algebraMap O Kf (χ g : O) = T.eK ((Y.chr g : X.Kˣ) : X.K) * T.detTw c (Y.u g) := by
  haveI := (P.setting ⟨0, T.nV_pos_of_prime hp⟩).frac_O
  have hinj := IsFractionRing.injective O Kf
  have hmem : ∀ g : S.G, ∃ y : O, algebraMap O Kf y = T.eK ((Y.chr g : X.Kˣ) : X.K) * T.detTw c (Y.u g) := by
    intro g
    obtain ⟨k, hk, hc⟩ := Y.chr_root g
    have h1 : T.eK ((Y.chr g : X.Kˣ) : X.K) ^ k = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
    have h2 : IsIntegral O (T.eK ((Y.chr g : X.Kˣ) : X.K)) :=
      ⟨Polynomial.X ^ k - 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by simp [h1]⟩
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    obtain ⟨z, hz⟩ := RetractionModules.detTw_mem T c (Y.u g)
    exact ⟨y * z, by rw [map_mul, hy, hz]⟩
  choose f hf using hmem
  let F : S.G →* O :=
    { toFun := f
      map_one' := hinj (by simp [hf, PlTie.detTw])
      map_mul' := fun a b => hinj (by
        rw [map_mul, hf, hf, hf]
        simp only [PlTie.detTw, map_mul, Units.val_mul, Subgroup.coe_mul, Finset.prod_mul_distrib, mul_zpow]
        ring) }
  exact ⟨F.toHomUnits, hf⟩

def chiLift (hp : p.Prime) (c : ℤ) : Y.ChiLift T c where
  χ d := (Y.exists_chi T hp c).choose.comp (Y.Gam d).subtype
  spec _ g := (Y.exists_chi T hp c).choose_spec g.1

def lev {c : ℤ} (x : Y.ChiLift T c) (a : Y.Comp) : Level P where
  Γ := Y.Gam (Y.rep a)
  act v := ((T.act hn v).comp Y.u).comp (Y.Gam (Y.rep a)).subtype
  χ := x.χ (Y.rep a)



end PSys

def gatOf {X : Fields} {n : ℕ} {lam : X.Tau → DomWeight n} {P : Places p O Kf} (T : PlTie X P) (hn : n = P.m + 1)
    (F : GFam X.K) (hF : F.Ok) (Y : ∀ b, PSys X n p lam (F.mem b)) {c : ℤ} (_hw : T.WtEq hn lam c) (hp : p.Prime) (e : ℕ) :
    GAtP p where
  O := O
  Kf := Kf
  P := P
  comp := Σ b, (Y b).Comp
  finComp := by
    haveI : ∀ b, Finite (Y b).Comp := fun b => (Y b).finite_comp (hF b)
    exact Fintype.ofFinite _
  lev a := (Y a.1).lev T hn ((Y a.1).chiLift T hp c) a.2
  e := e

end GlobalTheory.GO
