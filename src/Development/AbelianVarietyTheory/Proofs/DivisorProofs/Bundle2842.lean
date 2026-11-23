module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2823
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFiberMeasuresChangeOfForm
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open GlobalTheory.UPel.HT.TateCompare
open scoped TensorProduct
open scoped Classical

namespace GlobalTheory.LKGeo.GammaUniq

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

theorem exists_simSys_all {N : ℕ} (hN : 0 < N) (hK : N.Coprime p) {k : Type} [Field k] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (he : ∀ n q q' z z', e n q q' z → e n q q' z' → z = z') (I₁ I₂ : TateIsoO D k Q act e)
    (hI : ∀ y, I₁.ev N y = I₂.ev N y) :
    ∃ t : SimSys D N N, ∀ n, 0 < n → n.Coprime p → ∀ y, I₂.ev n y = I₁.ev n (t.g n y) := by
  choose g hg using exists_lift I₁ I₂
  choose u hu using exists_mult I₁ I₂
  have hdiv : ∀ {n m : ℕ}, (n * m).Coprime p → n.Coprime p := fun {n m} h =>
    Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) h
  have utow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → u (n * m) ≡ u n [MOD n] := by
    intro n m hn hm hc
    have h : I₁.ζ n ^ u (n * m) = I₁.ζ n ^ u n := by
      rw [hu n hn (hdiv hc), ← I₂.ζ_pow n m hn hm hc, ← hu _ (Nat.mul_pos hn hm) hc, ← pow_mul, mul_comm (u _) m,
        pow_mul, I₁.ζ_pow n m hn hm hc]
    rwa [pow_eq_pow_iff_modEq, ← (I₁.ζ_prim n hn (hdiv hc)).eq_orderOf] at h
  have gtow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z := by
    intro n m hn hm hc x
    rw [← ev_eq_iff I₁ hn (hdiv hc), hg n hn (hdiv hc), ← I₁.tower n m hn hm hc, hg _ (Nat.mul_pos hn hm) hc,
      I₂.tower n m hn hm hc]
  have sim2 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y,
      (n : ℤ) ∣ 2 * (D.EF (g n x) (g n y) - u n * D.EF x y) := by
    intro n hn hc x y
    have h₁ := I₁.isom n hn hc (g n x) (g n y)
    rw [hg n hn hc, hg n hn hc] at h₁
    have h := he _ _ _ _ _ h₁ (I₂.isom n hn hc x y)
    rw [← hu n hn hc, ← zpow_natCast, ← _root_.zpow_mul] at h
    rw [← (I₁.ζ_prim n hn hc).zpow_eq_one_iff_dvd, mul_sub, _root_.zpow_sub, h,
      show (u n : ℤ) * (2 * D.EF x y) = 2 * (u n * D.EF x y) by ring, mul_inv_cancel]
  refine ⟨{
    g := g
    u := u
    lin := fun n hn hc c x => ?_
    u_cop := fun n hn hc => ?_
    u_tower := utow
    surj := fun n hn hc x => ?_
    inj := fun n hn hc x z h => ?_
    sim := fun n hn hc x y => ?_
    tower := gtow
    one := fun x => ?_ }, fun n hn hc y => (hg n hn hc y).symm⟩
  · rw [← ev_eq_iff I₁ hn hc, hg n hn hc, I₁.lin, I₂.lin, hg n hn hc]
  · rw [← (I₁.ζ_prim n hn hc).pow_iff_coprime hn, hu n hn hc]
    exact I₂.ζ_prim n hn hc
  · obtain ⟨y, hy⟩ := (I₂.onto n hn hc _).1 ((I₁.onto n hn hc _).2 ⟨x, rfl⟩)
    refine ⟨y, ?_⟩
    rw [← ev_eq_iff I₁ hn hc, hg n hn hc, hy]
  · rw [← I₂.ker n hn hc, ← hg n hn hc, h]
    exact I₁.ev_nsmul_self hn hc z
  · by_cases hp : p = 2
    · subst hp
      have hco : IsCoprime (n : ℤ) 2 := by exact_mod_cast Nat.isCoprime_iff_coprime.2 hc
      exact hco.dvd_of_dvd_mul_left (sim2 n hn hc x y)
    · have hc2 : (n * 2).Coprime p :=
        Nat.Coprime.mul_left hc ((Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hp))
      have h := sim2 (n * 2) (by omega) hc2 x y
      obtain ⟨z, hz⟩ := gtow n 2 hn two_pos hc2 x
      obtain ⟨w, hw⟩ := gtow n 2 hn two_pos hc2 y
      obtain ⟨a, ha⟩ := (utow n 2 hn two_pos hc2).dvd
      obtain ⟨c, hcc⟩ := h
      rw [hz, hw] at hcc
      simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at hcc
      push_cast at hcc
      refine ⟨c - D.EF (g n x) w - D.EF z (g n y) - n * D.EF z w - a * D.EF x y, ?_⟩
      have h2 : (2 : ℤ) ≠ 0 := two_ne_zero
      apply mul_left_cancel₀ h2
      linear_combination hcc - 2 * D.EF x y * ha
  · rw [← ev_eq_iff I₁ hN hK, hg N hN hK, hI]

theorem isIntAf_mul {a c : AfP p} (ha : IsIntAf a) (hc : IsIntAf c) : IsIntAf (a * c) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hc v)

theorem isIntAf_intCast (c : ℤ) : IsIntAf (c : AfP p) := fun v => by
  rw [map_intCast]; exact intCast_mem _ c

theorem inAf_mem (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

theorem smul_mem {a : AfP p} (ha : IsIntAf a) {z : AfP p ⊗[ℚ] VQ D} (hz : z ∈ LaHat D) : a • z ∈ LaHat D := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a * c, x, isIntAf_mul ha hc, by rw [TensorProduct.smul_tmul', smul_eq_mul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem map_mem (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) (hA : ∀ x, A (inAf D x) ∈ LaHat D)
    {z : AfP p ⊗[ℚ] VQ D} (hz : z ∈ LaHat D) : A z ∈ LaHat D := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    have e : c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) = c • inAf D x := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e, map_smul]
    exact smul_mem hc (hA x)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := A)]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem eq_zero_of_dvd (a : AfP p) (h : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ c, IsIntAf c ∧ a = n • c) : a = 0 := by
  have key : ∀ v : AwayP p, AfP.eval v a = 0 := by
    intro v
    by_contra hne
    obtain ⟨l, hl0, hlp, hlv⟩ : ∃ l : ℕ, 0 < l ∧ l.Coprime p ∧ (l : ℤ) ∈ v.1.asIdeal := by
      have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
      have hmax : v.1.asIdeal.IsMaximal := v.1.isMaximal
      have hmp : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
      have hnle : ¬ v.1.asIdeal ≤ Ideal.span {(p : ℤ)} := fun hle => v.2 (hmax.eq_of_le hmp.ne_top hle)
      obtain ⟨x, hx, hxp⟩ := Set.not_subset.1 hnle
      have hxp' : ¬ (p : ℤ) ∣ x := fun hd => hxp (Ideal.mem_span_singleton.2 hd)
      refine ⟨x.natAbs, Int.natAbs_pos.2 (fun h0 => hxp' (h0 ▸ dvd_zero _)), ?_, ?_⟩
      · exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 (fun hd => hxp' (Int.natCast_dvd.2 hd))).symm
      · rcases Int.natAbs_eq x with h1 | h1
        · rw [← h1]; exact hx
        · rw [← neg_eq_iff_eq_neg.2 h1]; exact neg_mem hx
    have hlt : Valued.v ((l : ℕ) : v.1.adicCompletion ℚ) < 1 := by
      have e : ((l : ℕ) : v.1.adicCompletion ℚ) = algebraMap ℤ (v.1.adicCompletion ℚ) (l : ℤ) := by simp
      have e2 : Valued.v (algebraMap ℤ (v.1.adicCompletion ℚ) (l : ℤ)) = v.1.valuation ℚ (algebraMap ℤ ℚ (l : ℤ)) := by
        rw [IsScalarTower.algebraMap_apply ℤ ℚ (v.1.adicCompletion ℚ)]
        exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _
      rw [e, e2, HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hlv
    have hv0 : Valued.v (AfP.eval v a) ≠ 0 := (Valuation.ne_zero_iff _).2 hne
    obtain ⟨j, hj⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hv0)
    obtain ⟨c, hc, e⟩ := h (l ^ j) (pow_pos hl0 j) (Nat.Coprime.pow_left j hlp)
    have hc1 : Valued.v (AfP.eval v c) ≤ 1 := hc v
    have : Valued.v (AfP.eval v a) ≤ Valued.v ((l : ℕ) : v.1.adicCompletion ℚ) ^ j := by
      rw [e, map_nsmul, nsmul_eq_mul, map_mul, Nat.cast_pow, map_pow]
      exact mul_le_of_le_one_right' hc1
    exact absurd hj (not_lt.2 this)
  exact Subtype.ext (funext key)

def basAf {J : Type} (b : Module.Basis J ℤ D.La) : Module.Basis J (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (b.baseChange ℚ).baseChange (AfP p)

theorem basAf_apply {J : Type} (b : Module.Basis J ℤ D.La) (i : J) : basAf b i = inAf D (b i) := by
  simp [basAf, inAf]

theorem isIntAf_repr {J : Type} (b : Module.Basis J ℤ D.La) (i : J) {z : AfP p ⊗[ℚ] VQ D} (hz : z ∈ LaHat D) :
    IsIntAf ((basAf b).repr z i) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    have e : (basAf b).repr (c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D)) i = ((b.repr x i : ℤ) : AfP p) * c := by
      simp [basAf, Algebra.smul_def]
    rw [e]
    exact isIntAf_mul (isIntAf_intCast _) hc
  | zero => simpa using isIntAf_intCast (p := p) 0
  | add x y _ _ hx hy =>
    intro v
    rw [map_add (f := _), Finsupp.add_apply, map_add (f := _)]
    exact add_mem (hx v) (hy v)
  | neg x _ hx =>
    intro v
    rw [map_neg, Finsupp.neg_apply, map_neg]
    exact neg_mem (hx v)

theorem eq_zero_of_dvd_laHat (z : AfP p ⊗[ℚ] VQ D)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ w ∈ LaHat D, z = n • w) : z = 0 := by
  have := D.freeLa
  let b := Module.Free.chooseBasis ℤ D.La
  refine (basAf b).ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine eq_zero_of_dvd _ fun n hn hc => ?_
  obtain ⟨w, hw, rfl⟩ := h n hn hc
  exact ⟨_, isIntAf_repr b i hw, by rw [map_nsmul, Finsupp.smul_apply]⟩

theorem end_ext {A B : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)} (h : ∀ x, A (inAf D x) = B (inAf D x)) : A = B := by
  have := D.freeLa
  exact (basAf (Module.Free.chooseBasis ℤ D.La)).ext fun i => by rw [basAf_apply, h]

theorem actOn_injective {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hr : Function.Injective rep) (R : Type) [CommRing R] [Algebra ℚ R] :
    Function.Injective (actOn rep R) := by
  have h₁ : Function.Injective (rep.toLinearMap.lTensor R) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hr
  have j := (TensorProduct.isBaseChange ℚ V R).end
  have e : ∀ x, actOn rep R x = j.equiv (rep.toLinearMap.lTensor R x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r c =>
      rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul]
      ext v
      have := (TensorProduct.isBaseChange ℚ V R).endHom_comp_apply (rep c) v
      have e₁ : actOn rep R (r ⊗ₜ c) = r • (rep c).baseChange R := by
        rw [Algebra.smul_def]; rfl
      rw [e₁]
      simp at this ⊢
      simp [this, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  intro x y h
  rw [e, e] at h
  exact h₁ (j.equiv.injective h)

variable {G : HTGroup p} (L : Link D G)

theorem actG_injective : Function.Injective L.actG := by
  intro g h e
  have := D.finLa
  have h₁ : (g.1.1 : AfP p ⊗[ℚ] G.C) = h.1.1 := actOn_injective L.rep L.rep_inj (AfP p) e
  have h₁' : g.1.1 = h.1.1 := Units.ext h₁
  refine Subtype.ext (Prod.ext h₁' (Units.ext ?_))
  have hg := mem_uGroup.1 g.2
  have hh := mem_uGroup.1 h.2
  rw [h₁, hh] at hg
  have hinj : Function.Injective (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)) :=
    Algebra.TensorProduct.includeLeft_injective (S := ℚ) (algebraMap ℚ G.C).injective
  exact (hinj hg).symm

theorem inAf_add (x y : D.La) : inAf D (x + y) = inAf D x + inAf D y := by
  simp only [inAf, TensorProduct.tmul_add]

end GlobalTheory.LKGeo.GammaUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFramesDoublingPolynomialExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopDict

open Matrix

def IsEigB {n : ℕ} (s B : Matrix (Fin n) (Fin n) ℂ) (e : Fin n → Bool) : Prop :=
  IsUnit B.det ∧ s * B = B * Matrix.diagonal (fun a => if e a then (1 : ℂ) else -1)

theorem IsEigB.change_zero {n : ℕ} {s B B' : Matrix (Fin n) (Fin n) ℂ} {e e' : Fin n → Bool} (h : IsEigB s B e)
    (h' : IsEigB s B' e') {a b : Fin n} (hab : e a ≠ e' b) : (B⁻¹ * B') a b = 0 := by
  have h3 : B⁻¹ * s = Matrix.diagonal (fun a => if e a then (1 : ℂ) else -1) * B⁻¹ := by
    calc B⁻¹ * s = B⁻¹ * (s * B) * B⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h.1, Matrix.mul_one]
      _ = _ := by rw [h.2, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h.1, Matrix.one_mul]
  have h4 : Matrix.diagonal (fun a => if e a then (1 : ℂ) else -1) * (B⁻¹ * B') =
      (B⁻¹ * B') * Matrix.diagonal (fun a => if e' a then (1 : ℂ) else -1) := by
    rw [← Matrix.mul_assoc, ← h3, Matrix.mul_assoc, h'.2, Matrix.mul_assoc]
  have h5 := congrFun (congrFun h4 a) b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h5
  cases ha : e a <;> cases hb : e' b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at hab h5 <;> simp at h5 <;>
    first | linear_combination (1 / 2 : ℂ) * h5 | linear_combination (-1 / 2 : ℂ) * h5

theorem cplxO_unitMap_eig {m n : ℕ} {s B : Matrix (Fin n) (Fin n) ℂ} {e : Fin n → Bool} (h : IsEigB s B e)
    {s' B' : Matrix (Fin m) (Fin m) ℂ} {e' : Fin m → Bool} (h' : IsEigB s' B' e') (i : Fin m) (j : Fin n) :
    cplxO s s' (Formalism.IndefR.Datum.unitMap B B' i j) =
      ((if (e' i == e j) then 1 else -1 : ℂ) * Complex.I) • Formalism.IndefR.Datum.unitMap B B' i j := by
  obtain ⟨hu, h1⟩ := h
  obtain ⟨-, h2⟩ := h'
  have h3 : B⁻¹ * s = Matrix.diagonal (fun a => if e a then (1 : ℂ) else -1) * B⁻¹ := by
    calc B⁻¹ * s = B⁻¹ * (s * B) * B⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = _ := by rw [h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have e0 : Matrix.diagonal (fun a : Fin m => if e' a then (1 : ℂ) else -1) * single i j (1 : ℂ) *
      Matrix.diagonal (fun a : Fin n => if e a then (1 : ℂ) else -1) =
      (if (e' i == e j) then 1 else -1 : ℂ) • single i j (1 : ℂ) := by
    ext a b
    rw [mul_diagonal, diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hab : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hab
      cases hi : e' i <;> cases hj : e j <;> simp
    · simp [hab]
  unfold cplxO Formalism.IndefR.Datum.unitMap
  rw [mul_comm _ Complex.I, ← smul_smul]
  congr 1
  calc _ = (s' * B') * single i j (1 : ℂ) * (B⁻¹ * s) := by simp only [Matrix.mul_assoc]
    _ = B' * (Matrix.diagonal (fun a : Fin m => if e' a then (1 : ℂ) else -1) * single i j (1 : ℂ) *
      Matrix.diagonal (fun a : Fin n => if e a then (1 : ℂ) else -1)) * B⁻¹ := by
        rw [h2, h3]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [e0, Matrix.mul_smul, Matrix.smul_mul]

def cj (e : Bool) : ℂ →+* ℂ := if e then RingHom.id ℂ else starRingEnd ℂ

theorem cj_apply (e : Bool) (w : ℂ) : cj e w = if e then w else starRingEnd ℂ w := by cases e <;> rfl

def coef {m n : ℕ} (B₁ B₂ : Matrix (Fin n) (Fin n) ℂ) (C₁ C₂ : Matrix (Fin m) (Fin m) ℂ) (e₁ : Fin n → Bool)
    (d₁ : Fin m → Bool) (v b : Fin m × Fin n) : ℂ :=
  cj (d₁ b.1 == e₁ b.2) ((C₁⁻¹ * C₂) b.1 v.1 * (B₂⁻¹ * B₁) v.2 b.2)

theorem coef_mul {m n : ℕ} {s B₁ B₂ : Matrix (Fin n) (Fin n) ℂ} {s' C₁ C₂ : Matrix (Fin m) (Fin m) ℂ} {e₁ e₂ : Fin n → Bool}
    {d₁ d₂ : Fin m → Bool} (h₁ : IsEigB s B₁ e₁) (h₂ : IsEigB s B₂ e₂) (k₁ : IsEigB s' C₁ d₁) (k₂ : IsEigB s' C₂ d₂)
    (v w : Fin m × Fin n) :
    ∑ b, coef B₁ B₂ C₁ C₂ e₁ d₁ v b * coef B₂ B₁ C₂ C₁ e₂ d₂ b w = if w = v then 1 else 0 := by
  have e : ∀ b, coef B₁ B₂ C₁ C₂ e₁ d₁ v b * coef B₂ B₁ C₂ C₁ e₂ d₂ b w =
      cj (d₂ w.1 == e₂ w.2) (((C₂⁻¹ * C₁) w.1 b.1 * (C₁⁻¹ * C₂) b.1 v.1) * ((B₂⁻¹ * B₁) v.2 b.2 * (B₁⁻¹ * B₂) b.2 w.2)) := by
    intro b
    unfold coef
    by_cases a1 : d₂ w.1 = d₁ b.1
    · by_cases a2 : e₁ b.2 = e₂ w.2
      · rw [a1, a2, ← map_mul]; congr 1; ring
      · rw [h₁.change_zero h₂ a2]; simp
    · rw [k₂.change_zero k₁ a1]; simp
  have eC : (C₂⁻¹ * C₁) * (C₁⁻¹ * C₂) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ k₁.1, Matrix.nonsing_inv_mul _ k₂.1]
  have eB : (B₂⁻¹ * B₁) * (B₁⁻¹ * B₂) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ h₁.1, Matrix.nonsing_inv_mul _ h₂.1]
  simp only [e]
  have e3 : ∑ b : Fin m × Fin n, ((C₂⁻¹ * C₁) w.1 b.1 * (C₁⁻¹ * C₂) b.1 v.1) * ((B₂⁻¹ * B₁) v.2 b.2 * (B₁⁻¹ * B₂) b.2 w.2) =
      ((C₂⁻¹ * C₁) * (C₁⁻¹ * C₂)) w.1 v.1 * ((B₂⁻¹ * B₁) * (B₁⁻¹ * B₂)) v.2 w.2 := by
    rw [Matrix.mul_apply (M := C₂⁻¹ * C₁), Matrix.mul_apply (M := B₂⁻¹ * B₁), Finset.sum_mul_sum, Fintype.sum_prod_type]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, e3, eC, eB]
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  by_cases a1 : w1 = v1 <;> by_cases a2 : v2 = w2 <;> simp [Matrix.one_apply, a1, a2, @eq_comm _ w2 v2]

def sub {ι κ : Type} [Fintype κ] (c : ι → κ → κ → ℂ) : MvPolynomial (ι × κ) ℂ →ₐ[ℂ] MvPolynomial (ι × κ) ℂ :=
  MvPolynomial.aeval (fun v : ι × κ => ∑ b, c v.1 v.2 b • (MvPolynomial.X (v.1, b) : MvPolynomial (ι × κ) ℂ))

theorem sub_comp {ι κ : Type} [Fintype κ] [DecidableEq κ] (c c' : ι → κ → κ → ℂ)
    (h : ∀ τ v w, ∑ b, c τ v b * c' τ b w = if w = v then 1 else 0) : (sub c').comp (sub c) = AlgHom.id ℂ _ := by
  refine MvPolynomial.algHom_ext fun p => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sub, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_smul, Finset.smul_sum, smul_smul, AlgHom.id_apply]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, h, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]


open GlobalTheory.FockSubst GlobalTheory.FockCompare GlobalTheory.OrientedHeis in
theorem exists_change {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS B₁ B₂ : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT C₁ C₂ : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hS : ∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) (hT : ∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ))
    (h₁ : ∀ ρ, ∃ e, IsEigB (sS ρ) (B₁ ρ) e) (h₂ : ∀ ρ, ∃ e, IsEigB (sS ρ) (B₂ ρ) e)
    (k₁ : ∀ ρ, ∃ e, IsEigB (sT ρ) (C₁ ρ) e) (k₂ : ∀ ρ, ∃ e, IsEigB (sT ρ) (C₂ ρ) e) :
    ∃ σ : PolF D T.rank S.rank ≃ₗ[ℂ] PolF D T.rank S.rank, ∀ f, IsThetaFunO ψ S T f → ∀ P,
      pureTensorO ψ θ S T sS sT B₂ C₂ f P = pureTensorO ψ θ S T sS sT B₁ C₁ f (σ P) := by
  classical
  choose e₁ h₁ using h₁
  choose e₂ h₂ using h₂
  choose d₁ k₁ using k₁
  choose d₂ k₂ using k₂
  let c := fun τ => coef (B₁ τ) (B₂ τ) (C₁ τ) (C₂ τ) (e₁ τ) (d₁ τ)
  let c' := fun τ => coef (B₂ τ) (B₁ τ) (C₂ τ) (C₁ τ) (e₂ τ) (d₂ τ)
  refine ⟨(AlgEquiv.ofAlgHom (sub c) (sub c') (sub_comp c' c fun τ => coef_mul (h₂ τ) (h₁ τ) (k₂ τ) (k₁ τ))
    (sub_comp c c' fun τ => coef_mul (h₁ τ) (h₂ τ) (k₁ τ) (k₂ τ))).toLinearEquiv, fun f hf P => ?_⟩
  have hA : ∀ (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i f) :=
    fun _ _ _ _ h => aPlus_th hψ hθ _ _ _ h
  have Aadd : ∀ (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f f', IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T f' → aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i (f + f') =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i f +
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i f' :=
    fun _ _ _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  have Asm : ∀ (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i f :=
    fun _ _ _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  have Ac : ∀ (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i j f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' j f) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' j
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B B' i f) :=
    fun _ _ i j _ h => aPlus_comm (sS := sS) (sT := sT) hψ hθ i.1 _ hS hT j.1 _ h
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B₂ C₂ i g =
      ∑ b, c i.1 i.2 b • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) B₁ C₁ (i.1, b) g := by
    rintro ⟨ρ, a, j⟩ g hg
    simp only [aPlusAll, c]
    have eS : B₂ ρ = B₁ ρ * ((B₁ ρ)⁻¹ * B₂ ρ) := (Matrix.mul_nonsing_inv_cancel_left _ _ (h₁ ρ).1).symm
    have eT : C₂ ρ = C₁ ρ * ((C₁ ρ)⁻¹ * C₂ ρ) := (Matrix.mul_nonsing_inv_cancel_left _ _ (k₁ ρ).1).symm
    have eI : ((B₁ ρ)⁻¹ * B₂ ρ)⁻¹ = (B₂ ρ)⁻¹ * B₁ ρ := by
      rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (h₁ ρ).1]
    have eU := GlobalTheory.FockSubBoth.unitMap_mul_both (B₁ ρ) ((B₁ ρ)⁻¹ * B₂ ρ) (C₁ ρ) ((C₁ ρ)⁻¹ * C₂ ρ) a j
    rw [← eS, ← eT, eI] at eU
    rw [eU, aPlus_dir_sum hψ hθ ρ _ _ hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (cplxO_unitMap_eig (h₁ ρ) (k₁ ρ) b.1 b.2), coef, cj_apply]
  unfold pureTensorO
  exact pure_subst (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
    (hA _ _) (Ac _ _) (Aadd _ _) (Asm _ _) (hA _ _) (Ac _ _) (Aadd _ _) (Asm _ _)
    (fun v b => c v.1 v.2 b) (fun v b => (v.1, b)) key hf P

theorem IsEigB.neg {n : ℕ} {s B : Matrix (Fin n) (Fin n) ℂ} {e : Fin n → Bool} (h : IsEigB s B e) :
    IsEigB (-s) B (fun a => !e a) := by
  refine ⟨h.1, ?_⟩
  rw [Matrix.neg_mul, h.2, ← Matrix.mul_neg, Matrix.diagonal_neg]
  congr 2
  funext a
  cases h : e a <;> simp [h]

theorem isEigB_of_onb {n p : ℕ} {G s B : Matrix (Fin n) (Fin n) ℂ} (h : IsONBasis G s B p) :
    IsEigB s B (fun a => decide (a.val < p)) := by
  simpa [IsEigB] using GlobalTheory.FockSubBoth.onb_sign h

theorem isEigB_fr {D : D7} {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : IsEigB (A.cart τ) (A.onb τ) (A.ε τ) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hu, ?_⟩
  rw [Fr.cart, Fr.onb, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  rfl

theorem cart_frSgn_true {D : D7} {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : (frSgn true A).cart τ = -A.cart τ := by
  have e' : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
    ext a b
    by_cases h : a = b
    · subst h; cases h' : A.ε τ a <;> simp [Formalism.REAL.Jm, h']
    · simp [Formalism.REAL.Jm, h]
  show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ = -((A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * A.fr τ)
  rw [e', Matrix.mul_neg, Matrix.neg_mul]

theorem cart_frSgn_false {D : D7} {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : (frSgn false A).cart τ = A.cart τ := by
  show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor false (A.ε τ a)) * A.fr τ = (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * A.fr τ
  simp

theorem isCartanInv_neg {D : D7} {V : HSp D} {τ : D.what₂.Tau} {s : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : IsCartanInv (gramAt D V τ) s) : IsCartanInv (gramAt D (GlobalTheory.Grid.neg V) τ) (-s) := by
  have e : gramAt D (GlobalTheory.Grid.neg V) τ = -gramAt D V τ := by ext i j; simp [gramAt, GlobalTheory.Grid.neg_gram]
  rw [e]
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

theorem dict_frames {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hX : X.Is ψ θ α β νH S) (FA : Fr A) (FA' : Fr A') (FW : Fr WW) (hA : X.rA.s = FA.cart) (hA' : X.rA'.s = FA'.cart)
    (hW : X.rW.s = FW.cart) :
    ∃ (σ : PolF D WW.rank A.rank ≃ₗ[ℂ] PolF D WW.rank A.rank) (σ' : PolF D WW.rank A'.rank ≃ₗ[ℂ] PolF D WW.rank A'.rank), ∀ t : T,
      IsFinF ψ θ true FA FW (X.f t) ∧ IsFinF ψ θ false FA' FW (X.f' t) ∧
      (∀ P g h, X.ker ψ θ t P h g = thetaKO (X.ω t) g h (fockF ψ θ true FA FW (X.f t) (σ P))) ∧
      ∀ P g h, X.ker' ψ θ t P h g = thetaKO (X.ω' t) g h (fockF ψ θ false FA' FW (X.f' t) (σ' P)) := by
  have e1 : (frSgn true FA).cart = fun τ => -X.rA.s τ := funext fun τ => by rw [cart_frSgn_true, hA]
  have e2 : (frSgn false FA').cart = X.rA'.s := funext fun τ => by rw [cart_frSgn_false, hA']
  have hψ : IsStdChar D ψ (-1) := hX.isVac.1
  have hθ : IsInfFam θ := hX.isVac.2.inf
  have kW : ∀ ρ, ∃ e, IsEigB (X.rW.s ρ) (FW.onb ρ) e := fun ρ => ⟨_, hW ▸ isEigB_fr FW ρ⟩
  have kW' : ∀ ρ, ∃ e, IsEigB (X.rW.s ρ) (X.rW.B ρ) e := fun ρ => (hX.rigW.2.2 ρ).2.elim fun _ h => ⟨_, isEigB_of_onb h⟩
  obtain ⟨σ, hσ⟩ := exists_change (GlobalTheory.Grid.neg A) WW hψ hθ (fun τ => -X.rA.s τ) FA.onb X.rA.B X.rW.s FW.onb X.rW.B
    (fun ρ => isCartanInv_neg (hX.rigA.2.2 ρ).1) (fun ρ => (hX.rigW.2.2 ρ).1)
    (fun ρ => ⟨_, hA ▸ (isEigB_fr FA ρ).neg⟩) (fun ρ => (hX.rigA.2.2 ρ).2.elim fun _ h => ⟨_, (isEigB_of_onb h).neg⟩) kW kW'
  obtain ⟨σ', hσ'⟩ := exists_change A' WW hψ hθ X.rA'.s FA'.onb X.rA'.B X.rW.s FW.onb X.rW.B
    (fun ρ => (hX.rigA'.2.2 ρ).1) (fun ρ => (hX.rigW.2.2 ρ).1)
    (fun ρ => ⟨_, hA' ▸ isEigB_fr FA' ρ⟩) (fun ρ => (hX.rigA'.2.2 ρ).2.elim fun _ h => ⟨_, isEigB_of_onb h⟩) kW kW'
  refine ⟨σ, σ', fun t => ?_⟩
  have f1 := GlobalTheory.StageDict.fst_isFinF_frames X ψ θ α β νH S FA FW (congrFun e1) (fun τ => by rw [hW]) hX t
  have f2 := GlobalTheory.StageDict.isFinF_snd_frames X ψ θ α β νH S FA' FW (congrFun e2) (fun τ => by rw [hW]) hX t
  refine ⟨f1, f2, fun P g h => ?_, fun P g h => ?_⟩
  · unfold fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker
    rw [e1, ← hW, hσ _ f1.1]
    try rfl
  · unfold fockF GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker'
    rw [e2, ← hW, hσ' _ f2.1]
    try rfl

end GlobalTheory.TopDict

end
end

