module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0066
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.ConjRes
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix

private theorem low_ne {Γ R : Type} [Group Γ] [Field R] (y a : Γ → R) (hy : ∀ g h, y (g * h) = y g * a h + y h)
    (g0 g : Γ) (h0 : y g0 = 0) (ha : a g0 ≠ 1) (hg : y g ≠ 0) : y (g * g0 * g⁻¹) ≠ 0 := by
  intro h
  have e1 := hy (g * g0 * g⁻¹) g
  rw [inv_mul_cancel_right, hy, h, h0] at e1
  have e2 : y g * (a g0 - 1) = 0 := by linear_combination e1
  rcases mul_eq_zero.1 e2 with e | e
  · exact hg e
  · exact ha (sub_eq_zero.1 e)

private theorem conj_res {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [hF : IsGalois ℚ F]
    (g : G ℚ Ω) (s : G F Ω) : ∃ t : G F Ω, resQ F t = g * resQ F s * g⁻¹ := by
  haveI : IsGalois ℚ Ω := {}
  have hN : F.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois F).2 (by convert hF <;> exact Subsingleton.elim _ _)
  have hs : resQ F s ∈ F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact s.commutes ⟨x, hx⟩
  exact ⟨F.fixingSubgroupEquiv ⟨_, hN.conj_mem _ hs g⟩, rfl⟩

private theorem tn_21 {R : Type} [CommRing R] (a b : M2 R) : UpperTheory.V.Cu.tn a b 2 1 = -(a 1 0 * b 1 1) := by
  rfl

private theorem tn_30 {R : Type} [CommRing R] (a b : M2 R) : UpperTheory.V.Cu.tn a b 3 0 = a 1 0 * b 0 0 := by
  rfl

theorem UpperTheory.V.Cu.entOf4 : EntOf4 := by
  intro Ω _ _ _ l _ d T hT hO R _ f hf
  have hU : ∀ y : d.c₁.O, IsUnit y → f y ≠ 0 := fun y hy => (hy.map f).ne_zero
  have h00 : ∀ g, f (d.ρ₁ g 0 0) = f (inc d.h (UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k g)) := fun g => by
    have := hf _ (d.mod.red g).1
    rwa [map_sub, sub_eq_zero] at this
  have h11 : ∀ g, f (d.ρ₁ g 1 1) = 1 := fun g => by
    have := hf _ (d.mod.red g).2.1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have t00 : ∀ g, f (d.τ g 0 0) = 1 := fun g => by
    have := hf _ (d.tau.red g).1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have t11 : ∀ g, f (d.τ g 1 1) ≠ 0 := fun g => by
    by_cases hg : g ∈ d.K'.fixingSubgroup
    · rw [(d.tau.on g hg).1, t00]
      exact one_ne_zero
    · rw [(d.tau.off g hg).1, map_neg, t00]
      exact neg_ne_zero.2 one_ne_zero
  have hPhi : Raw.bar (UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k) (resQ T.F T.g0) ≠ 1 := by
    intro e
    apply hO.dist 0 3 (by decide)
    rw [hT.pr, d.tw.red0, d.tw.red3, e, mul_one]
  have ha : f (d.ρ₁ (resQ T.F T.g0) 0 0) ≠ 1 := by
    rw [h00]
    intro e
    have hu : IsUnit ((UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k (resQ T.F T.g0) : d.c.O) - 1) := by
      by_contra hn
      apply hPhi
      have : residue d.c.O ((UpperTheory.V.Cu.Phi d.D d.T₀.pr d.k (resQ T.F T.g0) : d.c.O) - 1) = 0 :=
        (residue_eq_zero_iff _).2 hn
      rwa [map_sub, map_one, sub_eq_zero] at this
    apply hU _ (hu.map (inc d.h))
    rw [map_sub, map_sub, e, map_one, map_one, sub_self]
  obtain ⟨g, hg⟩ := d.mod.ne
  have hg' : f (d.ρ₁ g 1 0) ≠ 0 := hU _ (by by_contra hn; exact hg hn)
  have key : ∃ t : G T.F Ω, f (d.ρ₁ (resQ T.F t) 1 0) ≠ 0 := by
    by_cases h0 : f (d.ρ₁ (resQ T.F T.g0) 1 0) = 0
    · obtain ⟨t, ht⟩ := conj_res T.F g T.g0
      refine ⟨t, ?_⟩
      rw [ht]
      refine low_ne (fun g => f (d.ρ₁ g 1 0)) (fun g => f (d.ρ₁ g 0 0)) (fun g h => ?_) _ g h0 ha hg'
      simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, map_add (f := _), h11, one_mul]
    · exact ⟨T.g0, h0⟩
  obtain ⟨t, ht⟩ := key
  have hδ : f (toC d.h d.δ (resQ T.F t) : d.c₁.O) ≠ 0 := hU _ (Units.isUnit _)
  have ent : ∀ i j, ((d.Q T).map f).r t i j =
      f (toC d.h d.δ (resQ T.F t) : d.c₁.O) * f (UpperTheory.V.Cu.tn (d.ρ₁ (resQ T.F t)) (d.τ (resQ T.F t)) i j) := fun i j => by
    rw [← map_mul]
    rfl
  refine ⟨⟨t, 2, 1, by decide, ?_⟩, ⟨t, 3, 0, by decide, ?_⟩⟩
  · rw [ent, tn_21, map_neg, map_mul]
    exact mul_ne_zero hδ (neg_ne_zero.2 (mul_ne_zero ht (t11 _)))
  · rw [ent, tn_30, map_mul, t00, mul_one]
    exact mul_ne_zero hδ ht

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.EqOfRd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open UpperTheory.V.Ws

namespace UpperTheory.V.Cu.RankFourTwistExistence

section SlopeTestRemainingChoices

variable {Γ O : Type} [Group Γ] [TopologicalSpace Γ] [CommRing O] {I : Ideal O} {γ δ : Γ →* Oˣ}

theorem ac_mul (h : AdicCont I fun g => (γ g : O)) (h' : AdicCont I fun g => (δ g : O)) :
    AdicCont I fun g => ((γ * δ) g : O) := fun N => by
  simp only [MonoidHom.mul_apply, Units.val_mul, map_mul]
  exact (h N).mul (h' N)

theorem ac_zpow (h : AdicCont I fun g => (γ g : O)) (n : ℤ) : AdicCont I fun g => ((γ ^ n) g : O) := fun N => by
  have h1 : IsLocallyConstant fun g => Units.map (Ideal.Quotient.mk (I ^ N)).toMonoidHom (γ g) :=
    IsLocallyConstant.desc _ Units.val (h N) Units.val_injective
  have h2 := h1.comp fun u => ((u ^ n : (O ⧸ I ^ N)ˣ) : O ⧸ I ^ N)
  refine (congrArg IsLocallyConstant (funext fun g => ?_)).mp h2
  simp only [Function.comp_apply, MonoidHom.zpow_apply]
  rw [← map_zpow]
  rfl

theorem ac_ker [IsTopologicalGroup Γ] (h : IsOpen (γ.ker : Set Γ)) : AdicCont I fun g => (γ g : O) := fun N => by
  rw [IsLocallyConstant.iff_exists_open]
  refine fun x => ⟨(fun y => x⁻¹ * y) ⁻¹' γ.ker, h.preimage (continuous_const_mul _), by simp, fun y hy => ?_⟩
  have h1 : γ (x⁻¹ * y) = 1 := hy
  beta_reduce
  rw [← mul_inv_cancel_left x y, map_mul γ, h1, mul_one]

end SlopeTestRemainingChoices

noncomputable def rd {l : ℕ} [Fact l.Prime] (c : Coef l) : c.Oˣ →* (ResidueField c.O)ˣ :=
  Units.map (residue c.O).toMonoidHom

theorem eq_of_rd {l : ℕ} [Fact l.Prime] {c : Coef l} {x y : c.Oˣ} {m : ℕ} (hm : l.Coprime m) (hx : x ^ m = 1)
    (hy : y ^ m = 1) (h : rd c x = rd c y) : x = y :=
  (congrFacts (AlgebraicClosure ℚ) l c).2.2.2.1 x y m ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hm) hx hy
    (Ideal.Quotient.eq.1 (congrArg Units.val h))

theorem grpF {M : Type} [CommGroup M] (η ω ξ ψ : M) (e k : ℤ) :
    (η ^ (e + 2 - k)) ^ 2 * ((η ^ 2 * ω) ^ (k - 1) * (ξ * ψ)) =
      η ^ 2 * ω * ω⁻¹ * ξ * ((η ^ 2 * ω) ^ e * ψ) * (ω ^ (k - 1) * (ω ^ e)⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_pow, ofMul_zpow, ofMul_inv]
  module

theorem grpT {M : Type} [CommGroup M] (η ω ξ ψ : M) (e k : ℤ) :
    (ω ^ e * ψ * η ^ (e + 2 - k)) ^ 2 * ((η ^ 2 * ω) ^ (k - 1) * (ξ * ψ⁻¹)) =
      η ^ 2 * ω * ω⁻¹ * ξ * ((η ^ 2 * ω) ^ e * ψ) * (ω ^ (k - 1) * (ω ^ e)⁻¹) * (ω ^ e) ^ 2 := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_pow, ofMul_zpow, ofMul_inv]
  module

theorem cancel3 {M : Type} [CommGroup M] {a b d p : M} (h : a * b = d ^ 2 * p) (hb : b = d) : a = d * p := by
  subst hb
  apply mul_right_cancel (b := b)
  rw [h, sq, mul_right_comm]

end UpperTheory.V.Cu.RankFourTwistExistence

open UpperTheory.V.Cu.RankFourTwistExistence in
theorem UpperTheory.V.Cu.twEx4 : UpperTheory.V.Cu.TwEx4 := by
  intro Ω _ _ _ l hl c D T h3 k hk1 hk
  have h : D.Good := h3.1
  obtain ⟨-, he2, -, ⟨mψ, -, hmψ, hψ⟩, -⟩ := UpperTheory.V.Ws.large₂.host3 D h3
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcont, -, homo, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D h
  obtain ⟨mξ, hmξ, hξ⟩ := h.xi_ord
  have hl1 : l.Coprime (l - 1) := (Nat.coprime_self_sub_right hl.out.one_le).2 (Nat.coprime_one_right l)
  set ε := chiO ℚ Ω l c.O with hε
  set μ : G ℚ Ω →* c.Oˣ := D.al * D.ξ ^ (-1 : ℤ) with hμ
  set P : G ℚ Ω →* c.Oˣ := D.om ^ (D.e : ℤ) * D.ψ with hP
  have al_eq : ∀ g, D.al g = ε g * (D.om g)⁻¹ * D.ξ g := fun _ => rfl
  have mu_eq : ∀ g, μ g = ε g * (D.om g)⁻¹ := fun g => by
    rw [hμ, MonoidHom.mul_apply, MonoidHom.zpow_apply, al_eq, zpow_neg_one, mul_inv_cancel_right]
  have charpoly_eq_of_isIso : ∀ g, P g = D.om g ^ D.e * D.ψ g := fun g => by
    rw [hP, MonoidHom.mul_apply, MonoidHom.zpow_apply, zpow_natCast]
  have P_eqz : ∀ g, P g = D.om g ^ (D.e : ℤ) * D.ψ g := fun g => by
    rw [hP, MonoidHom.mul_apply, MonoidHom.zpow_apply]
  have Psi_z : ∀ g, D.Psi g = ε g ^ (D.e : ℤ) * D.ψ g := fun _ => rfl
  have Psi_eq : ∀ g, D.Psi g = μ g ^ D.e * P g := fun g => by
    have : D.Psi g = ε g ^ D.e * D.ψ g := by rw [← zpow_natCast]; rfl
    rw [this, mu_eq, charpoly_eq_of_isIso, mul_pow, inv_pow, mul_assoc, inv_mul_cancel_left]
  have al_eq' : ∀ g, D.al g = μ g * D.ξ g := fun g => by rw [al_eq, mu_eq]
  have th_eq : ∀ g, D.th g = D.al g * D.Psi g := fun _ => rfl
  have rmu : ∀ g, rd c (μ g) = 1 := fun g => by
    have : rd c (D.om g) = rd c (ε g) := Units.ext (h.om_bar g)
    rw [mu_eq, map_mul, map_inv, this, mul_inv_cancel]
  have ral : ∀ g, rd c (D.al g) = rd c (D.ξ g) := fun g => by rw [al_eq', map_mul, rmu, one_mul]
  have rPsi : ∀ g, rd c (D.Psi g) = rd c (P g) := fun g => by rw [Psi_eq, map_mul, map_pow, rmu, one_pow, one_mul]
  have omp : ∀ g, D.om g ^ (l - 1) = 1 := fun g => DFunLike.congr_fun h.om_pow g
  have hM : l.Coprime ((l - 1) * mψ * mξ) := (hl1.mul_right hmψ).mul_right hmξ
  have PM : ∀ g, P g ^ ((l - 1) * mψ * mξ) = 1 := fun g => by
    have h1 : D.ψ g ^ mψ = 1 := DFunLike.congr_fun hψ g
    rw [charpoly_eq_of_isIso, mul_pow, ← pow_mul, mul_comm D.e, mul_assoc, mul_assoc, pow_mul, omp, one_pow, one_mul, mul_assoc, mul_left_comm,
      pow_mul, h1, one_pow]
  have xM : ∀ g, D.ξ g ^ ((l - 1) * mψ * mξ) = 1 := fun g => by
    have h1 : D.ξ g ^ mξ = 1 := DFunLike.congr_fun hξ g
    rw [mul_comm, pow_mul, h1, one_pow]
  have h2 : IsUnit (2 : c.O) := by
    have : IsUnit ((2 : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes hl.out Nat.prime_two).2 h.l_odd
    simpa [map_ofNat] using this.map (algebraMap ℤ_[l] c.O)
  obtain ⟨η, η2, ηr, ηc, η1⟩ := UpperTheory.exists_square_root_character c.O h2 (G ℚ Ω) μ (fun g => congrArg Units.val (rmu g))
    (ac_mul (hcont 2) (ac_zpow (ac_ker h.xi_open) _))
  have rη : ∀ g, rd c (η g) = 1 := fun g => Units.ext (ηr g)
  have eps_eq : ∀ g, ε g = η g ^ 2 * D.om g := fun g => by rw [η2, mu_eq, inv_mul_cancel_right]
  have epz : ∀ g, ε g ^ (k - 1) = ε g ^ ((k : ℤ) - 1) := fun g => by
    rw [← zpow_natCast, Nat.cast_sub hk1, Nat.cast_one]
  have hkz : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
  have omz : ∀ g, D.om g ^ ((k : ℤ) - 1) = D.om g ^ (D.e : ℤ) := fun g => by
    rw [hkz, zpow_natCast, zpow_natCast]
    exact pow_eq_pow_iff_modEq.2 (hk.of_dvd (orderOf_dvd_of_pow_eq_one (omp g)))
  have om2 : ∀ g, (D.om g ^ (D.e : ℤ)) ^ 2 = 1 := fun g => by
    obtain ⟨n, hn⟩ := he2
    rw [zpow_natCast, ← pow_mul, mul_comm, hn, pow_mul, omp, one_pow]
  set j : ℤ := (D.e : ℤ) + 2 - k with hj
  have hc03 : ∀ g, chi D T.pr 0 g * chi D T.pr 3 g = D.th g := fun g => by
    cases T.pr
    · change D.th g * 1 = D.th g
      rw [mul_one]
    · rfl
  obtain ⟨t, tc, tmul, tred, t1⟩ : ∃ t : G ℚ Ω →* c.Oˣ, AdicCont (maximalIdeal c.O) (fun g => (t g : c.O)) ∧
      (∀ g, (t g * η g ^ j) ^ 2 * UpperTheory.V.Cu.Phi D T.pr k g = D.th g) ∧
      (∀ g, rd c (chi D T.pr 3 g) = rd c (t g)) ∧ ∀ g, P g = 1 → t g = 1 := by
    cases hpr : T.pr
    · refine ⟨1, ac_ker (by rw [MonoidHom.ker_one]; exact isOpen_univ), fun g => ?_, fun g => ?_, fun _ _ => rfl⟩
      · change (1 * η g ^ j) ^ 2 * (ε g ^ (k - 1) * (D.ξ g * D.ψ g)) = ε g * (D.om g)⁻¹ * D.ξ g * (ε g ^ (D.e : ℤ) * D.ψ g)
        rw [one_mul, epz, eps_eq, hj, grpF, omz, mul_inv_cancel, mul_one]
      · rfl
    · refine ⟨P, ac_mul (ac_zpow (ac_ker homo) _) (ac_ker h.psi_open), fun g => ?_, fun g => rPsi g, fun _ h => h⟩
      · change (P g * η g ^ j) ^ 2 * (ε g ^ (k - 1) * (D.ξ g * (D.ψ g)⁻¹)) =
          ε g * (D.om g)⁻¹ * D.ξ g * (ε g ^ (D.e : ℤ) * D.ψ g)
        rw [P_eqz, epz, eps_eq, hj, grpT, omz, mul_inv_cancel, mul_one, om2, mul_one]
  have δ_eq : ∀ g, (t * η ^ j) g = t g * η g ^ j := fun _ => rfl
  have rδ : ∀ g, rd c ((t * η ^ j) g) = rd c (t g) := fun g => by rw [δ_eq, map_mul, map_zpow, rη, one_zpow, mul_one]
  refine ⟨t * η ^ j, ⟨ac_mul tc (ac_zpow ηc j), fun g => ?_, fun g => ?_, fun g => ?_, fun g hg hr => ?_,
    D.om.ker ⊓ D.ψ.ker, j, homo.inter h.psi_open, fun g hg => ?_⟩⟩
  · rw [δ_eq]
    exact tmul g
  · have e0 : chi D T.pr 0 g * chi D T.pr 3 g = (t * η ^ j) g ^ 2 * UpperTheory.V.Cu.Phi D T.pr k g := (hc03 g).trans (tmul g).symm
    have e1 := congrArg (rd c) e0
    rw [map_mul, map_mul, map_pow] at e1
    exact congrArg Units.val (cancel3 e1 ((tred g).trans (rδ g).symm))
  · exact congrArg Units.val ((tred g).trans (rδ g).symm)
  · have hr' : ∀ i, rd c (D.ps i g) = 1 := fun i => Units.ext (by
      have := congrFun (congrFun hr i) i
      change residue c.O (D.ps i g : c.O) = 1
      simpa [Raw.rbar, Raw.r0, diagRep] using this)
    have e1 : ε g = 1 := by rw [hε, chiO, MonoidHom.comp_apply, hg, map_one]
    have o1 : D.om g = 1 := eq_of_rd hl1 (omp g) (one_pow _) (e1 ▸ Units.ext (h.om_bar g))
    have p1 : P g = 1 := eq_of_rd hM (PM g) (one_pow _) (by rw [← rPsi, map_one]; exact hr' 1)
    have x1 : D.ξ g = 1 := eq_of_rd hM (xM g) (one_pow _) (by rw [← ral, map_one]; exact hr' 2)
    have s1 : D.ψ g = 1 := by rw [charpoly_eq_of_isIso, o1, one_pow, one_mul] at p1; exact p1
    refine ⟨?_, ?_⟩
    · rw [δ_eq, t1 g p1, η1 g (by rw [mu_eq, e1, o1, inv_one, mul_one]), one_zpow, mul_one]
    · cases T.pr
      · change D.ξ g * D.ψ g = 1
        rw [x1, s1, mul_one]
      · change D.ξ g * (D.ψ g)⁻¹ = 1
        rw [x1, s1, inv_one, mul_one]
  · have o1 : D.om g = 1 := hg.1
    have o2 : D.ψ g = 1 := hg.2
    rw [← hε, δ_eq, t1 g (by rw [charpoly_eq_of_isIso, o1, o2, one_pow, mul_one]), one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, η2, mu_eq, o1, inv_one, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FlagConjSmulTensorSymmetricEq
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu.SymplecticFlagConjugation

section Alg

variable {R : Type} [CommRing R]

theorem flg_eq (x s : R) : flg x s = !![1, 0, 0, 0; s, 1, 0, 0; -(x * s), -x, 1, 0; x, 0, -s, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, low, nA, Matrix.mul_apply, Fin.sum_univ_four]

theorem adj_flg (x s : R) : adj (flg x s) = !![1, 0, 0, 0; -s, 1, 0, 0; 0, x, 1, 0; -x, x * s, s, 1] := by
  rw [flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

theorem isGSp_flg (x s : R) : IsGSp 1 (flg x s) := by
  unfold IsGSp
  rw [adj_flg, flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gsp_tn (d : R) (g t : Matrix (Fin 2) (Fin 2) R) (h00 : t 0 0 * t 0 0 - t 1 0 * t 1 0 = 1)
    (h01 : t 0 0 * t 0 1 - t 1 0 * t 1 1 = 0) (h11 : t 0 1 * t 0 1 - t 1 1 * t 1 1 = -1) :
    IsGSp (d ^ 2 * g.det) (d • tn g t) := by
  unfold IsGSp
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
    | ring1
    | linear_combination (d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) * h00
    | linear_combination (d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) * h01
    | linear_combination (-(d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0))) * h01
    | linear_combination (-(d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0))) * h11

theorem flag_conj_smul_tensor_symmetric_eq (x s d a b p q r : R) (hs : s * s = 1) :
    adj (flg x s) * (d • tn !![p, q; (p + q * x) * x - r * x, r] !![a, b; b, a]) * flg x s =
      d • !![(a + b * s) * (p + q * x), b * (p + q * x), -(q * (a * s + b)), a * q;
        0, (a - b * s) * (p + q * x), 0, -(q * (a * s - b));
        0, 0, (a + b * s) * (r - x * q), -(b * (r - x * q));
        0, 0, 0, (a - b * s) * (r - x * q)] := by
  rw [Matrix.mul_smul, Matrix.smul_mul, adj_flg, flg_eq]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
    | ring1
    | linear_combination (-(b * (p + q * x))) * hs
    | linear_combination (-(b * (q * x - r))) * hs
    | linear_combination (b * (p + q * x)) * hs
    | linear_combination (b * (q * x - r)) * hs
    | linear_combination (q * a) * hs

theorem conj_flg (x s d : R) (g t : Matrix (Fin 2) (Fin 2) R) (hs : s * s = 1)
    (hf : g 1 0 + g 1 1 * x = (g 0 0 + g 0 1 * x) * x) (ht : t 1 1 = t 0 0 ∧ t 1 0 = t 0 1) :
    adj (flg x s) * (d • tn g t) * flg x s =
      d • !![(t 0 0 + t 0 1 * s) * (g 0 0 + g 0 1 * x), t 0 1 * (g 0 0 + g 0 1 * x), -(g 0 1 * (t 0 0 * s + t 0 1)), t 0 0 * g 0 1;
        0, (t 0 0 - t 0 1 * s) * (g 0 0 + g 0 1 * x), 0, -(g 0 1 * (t 0 0 * s - t 0 1));
        0, 0, (t 0 0 + t 0 1 * s) * (g 1 1 - x * g 0 1), -(t 0 1 * (g 1 1 - x * g 0 1));
        0, 0, 0, (t 0 0 - t 0 1 * s) * (g 1 1 - x * g 0 1)] := by
  have e1 : g = !![g 0 0, g 0 1; (g 0 0 + g 0 1 * x) * x - g 1 1 * x, g 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linear_combination hf
  have e2 : t = !![t 0 0, t 0 1; t 0 1, t 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht.1, ht.2]
  conv_lhs => rw [e1, e2]
  exact flag_conj_smul_tensor_symmetric_eq x s d (t 0 0) (t 0 1) (g 0 0) (g 0 1) (g 1 1) hs

theorem form_eqs (t : Matrix (Fin 2) (Fin 2) R) (h : tᵀ * !![1, 0; 0, -1] * t = !![1, 0; 0, -1]) :
    t 0 0 * t 0 0 - t 1 0 * t 1 0 = 1 ∧ t 0 0 * t 0 1 - t 1 0 * t 1 1 = 0 ∧ t 0 1 * t 0 1 - t 1 1 * t 1 1 = -1 := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  exact ⟨by linear_combination e00, by linear_combination e01, by linear_combination e11⟩

theorem symplecticAdjoint_map_ringHom {R' : Type} [CommRing R'] (f : R →+* R') (X : M4 R) : adj (X.map f) = (adj X).map f := by
  ext i j
  simp [adj_apply]

theorem conj_map {R' : Type} [CommRing R'] (f : R →+* R') (N M : M4 R) :
    adj (N.map f) * M.map f * N.map f = (adj N * M * N).map f := by
  rw [symplecticAdjoint_map_ringHom, ← Matrix.map_mul, ← Matrix.map_mul]

theorem gsp_map {R' : Type} [CommRing R'] (f : R →+* R') {ν : R} {M : M4 R} (h : IsGSp ν M) : IsGSp (f ν) (M.map f) := by
  unfold IsGSp at *
  rw [symplecticAdjoint_map_ringHom, ← Matrix.map_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem pow_diag {g : M2 R} (h : g 0 1 = 0 ∧ g 1 0 = 0) (n : ℕ) :
    (g ^ n) 0 1 = 0 ∧ (g ^ n) 1 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h.1, h.2, ih.1, ih.2]

theorem res_inv {O : Type} [CommRing O] [IsLocalRing O] (u : Oˣ) (h : residue O (u : O) = 1) :
    residue O ((u⁻¹ : Oˣ) : O) = 1 := by
  have e := congrArg (residue O) (Units.inv_mul u)
  rwa [map_mul, h, mul_one, map_one] at e

end Alg

end UpperTheory.V.Cu.SymplecticFlagConjugation

open UpperTheory.V.Cu.SymplecticFlagConjugation in
theorem UpperTheory.V.Cu.pairOf4 : UpperTheory.V.Cu.PairOf4 := by
  intro Ω _ _ _ l _ d T hT hok W R _ f hdet hθ
  have hr : ∀ g, ((d.Q T).map f).r g =
      ((inc d.h (d.δ (resQ T.F g) : d.c.O)) • tn (d.ρ₁ (resQ T.F g)) (d.τ (resQ T.F g))).map f := fun g => rfl
  have hn : ∀ v, ((d.Q T).map f).n v = (flg (d.x (T.pl v)) (d.s (T.pl v))).map f := fun v => rfl
  have hF : ∀ g : G T.F Ω, resQ T.F g ∈ T.F.fixingSubgroup := fun g x => g.commutes x
  have hcyc : ∀ g : G T.F Ω, cycZ ℚ Ω l (resQ T.F g) = cycZ T.F Ω l g := fun g => rfl
  have hD : ∀ A, ∀ g ∈ Dec (F := T.F) A, resQ T.F g ∈ Dec (F := ℚ) A := fun A g h => mem_Dec.2 (mem_Dec.1 h)
  have hI : ∀ A, ∀ g ∈ Ine (F := T.F) A, resQ T.F g ∈ Ine (F := ℚ) A := fun A g h => mem_Ine.2 (mem_Ine.1 h)
  have hsgn : ∀ A, d.s A * d.s A = 1 := fun A => by
    rcases d.tau.sgn A with h | h <;> rw [h] <;> ring
  refine ⟨fun g => ?_, ?_, ?_, fun v => ?_, fun v s hs => ?_, fun v s hs i => ?_⟩
  · obtain ⟨h00, h01, h11⟩ := form_eqs _ (d.tau.form (resQ T.F g))
    have h1 := gsp_map f (gsp_tn (inc d.h (d.δ (resQ T.F g) : d.c.O)) (d.ρ₁ (resQ T.F g)) _ h00 h01 h11)
    have key : inc d.h (d.δ (resQ T.F g) : d.c.O) ^ 2 * inc d.h (Phi d.D d.T₀.pr d.k (resQ T.F g) : d.c.O) =
        inc d.h (d.D.th (resQ T.F g) : d.c.O) := by
      rw [← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, d.tw.mul]
    rw [map_mul, hdet _ (hF g), ← map_mul, key] at h1
    exact h1
  · rintro g ⟨A, hA, hg, h1⟩
    have hl := hA l (Finset.mem_insert_self _ _)
    have hI' := hI A g hg
    have h2 := d.tw.kill _ ((places ℚ Ω l A).2.2.2 hl hI') h1
    have hK : resQ T.F g ∈ d.K'.fixingSubgroup := by
      by_contra hn'
      have hres : resQ d.T₀.F (resLe hT.le g) = resQ T.F g := AlgEquiv.ext fun _ => rfl
      have hoff := d.quad.off (resLe hT.le g) (by rwa [hres])
      have hb : ∀ j, residue d.c.O (d.D.ps j (resQ T.F g) : d.c.O) = 1 := fun j => by
        have e := congrFun (congrFun h1 j) j
        simpa [Raw.rbar, Raw.r0, diagRep] using e
      have hon : d.T₀.rb wAl (resLe hT.le g) = 1 := by
        show residue d.c.O (((chi d.D d.T₀.pr 0 (resQ T.F g) * (chi d.D d.T₀.pr 1 (resQ T.F g))⁻¹) ^ (1 : ℤ) *
          (chi d.D d.T₀.pr 0 (resQ T.F g) * (chi d.D d.T₀.pr 2 (resQ T.F g))⁻¹) ^ (0 : ℤ) : d.c.Oˣ) : d.c.O) = 1
        have hb' : ∀ i, residue d.c.O (chi d.D d.T₀.pr i (resQ T.F g) : d.c.O) = 1 := fun i => hb (lab d.T₀.pr i)
        rw [zpow_one, zpow_zero, mul_one, Units.val_mul, map_mul, hb', res_inv _ (hb' 1), mul_one]
      have := (UpperTheory.V.Ws.P1.coefRes d.c).2.1
      exact Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq (ResidueField d.c.O) l]; exact d.ctx.1.l_odd)
        (hoff.symm.trans hon)
    have h3 := d.tau.unr A hl _ hI' hK
    have h4 := d.mod.away A hl _ hI' h2.2 (hθ A hA g hg)
    refine (hr g).trans ?_
    rw [h2.1, h3, h4, tn_one]
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · obtain ⟨j, hj⟩ := hT.g0
    have hρ := pow_diag d.mod.nrm (l ^ j)
    have hτ := pow_diag (g := d.τ (resQ d.T₀.F d.T₀.g0)) (by rw [d.tau.nrm]; simp) (l ^ j)
    rw [← map_pow, ← hj] at hρ hτ
    intro a b hab
    refine (congrFun (congrFun (hr T.g0) a) b).trans ?_
    generalize resQ T.F T.g0 = g1 at hρ hτ ⊢
    fin_cases a <;> fin_cases b <;> simp [tn, hρ.1, hρ.2, hτ.1, hτ.2] at hab ⊢
  · change IsLow ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f)
    refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
    · simpa using gsp_map f (isGSp_flg (d.x (T.pl v)) (d.s (T.pl v)))
    · rw [flg_eq]
      fin_cases i <;> simp
    · rw [flg_eq]
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp
  · have hsD := hD _ s hs
    change IsUp (adj ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f) * ((inc d.h (d.δ (resQ T.F s) : d.c.O)) • tn (d.ρ₁ (resQ T.F s)) (d.τ (resQ T.F s))).map f * (flg (d.x (T.pl v)) (d.s (T.pl v))).map f)
    rw [conj_map, conj_flg _ _ _ _ _ (hsgn _) (d.mod.flag _ (T.ovl v) _ hsD)
      (d.tau.on _ (d.quad.split _ (T.ovl v) hsD))]
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp
  · obtain ⟨hi, hc⟩ := UpperTheory.inertia_acts_trivially_on_roots_of_unity T.F Ω l d.ctx.1.l_odd _ (T.ovl v) s hs
    have hc' := (hcyc s).trans hc
    have hsD : resQ T.F s ∈ Dec (F := ℚ) (T.pl v) := hD _ s hs.1
    have hsI := hI _ s hi
    have hK := d.quad.split _ (T.ovl v) hsD
    have hδ := (d.tw.kill _ hc' (hok.ineL _ (T.ovl v) s hi)).1
    have hm := d.mod.ine _ (T.ovl v) _ hsI
    have h3 : chiO ℚ Ω l d.c₁.O (resQ T.F s) = 1 := by
      show Units.map _ (cycZ ℚ Ω l _) = 1
      rw [hc', map_one]
    have ht := d.tau.ine _ (T.ovl v) _ hsI
    rw [h3, one_pow, Units.val_one] at ht hm
    obtain ⟨h00, -, -⟩ := form_eqs _ (d.tau.form (resQ T.F s))
    have hon := d.tau.on _ hK
    have hss := hsgn (T.pl v)
    have h4 : d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.s (T.pl v) = 1 := by
      linear_combination (-(d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.s (T.pl v))) * ht + h00 +
        (d.τ (resQ T.F s) 1 0 + d.τ (resQ T.F s) 0 1) * hon.2 + (-(d.τ (resQ T.F s) 0 1 ^ 2)) * hss
    change (adj ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f) * ((inc d.h (d.δ (resQ T.F s) : d.c.O)) • tn (d.ρ₁ (resQ T.F s)) (d.τ (resQ T.F s))).map f * (flg (d.x (T.pl v)) (d.s (T.pl v))).map f) i i = 1
    rw [conj_map, conj_flg _ _ _ _ _ hss (d.mod.flag _ (T.ovl v) _ hsD) hon, hm.1, hm.2, ht, h4, hδ]
    fin_cases i <;> simp

end
end

