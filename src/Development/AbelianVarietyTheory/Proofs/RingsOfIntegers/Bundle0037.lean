module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CardPrimaryTorsionTuplesKilledByMatrix
section
set_option autoImplicit false

namespace GlobalTheory.TorsCount

theorem card_primary (C : Type) [AddCommGroup C] [Finite C] (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nat.card {c : C // ∃ j : ℕ, ℓ ^ j • c = 0} = ℓ ^ (Nat.card C).factorization ℓ := by
  haveI := Fact.mk hℓ
  let P : Sylow ℓ (Multiplicative C) :=
    ⟨CommGroup.primaryComponent (Multiplicative C) ℓ, CommGroup.primaryComponent.isPGroup, fun {Q} hQ hle =>
      fun x hx => by
        obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
        exact CommGroup.mem_primaryComponent.2 ⟨k, congrArg Subtype.val hk⟩⟩
  have h := Sylow.card_eq_multiplicity P
  rw [Nat.card_congr (Multiplicative.toAdd (α := C))] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd fun c =>
    (CommGroup.mem_primaryComponent (G := Multiplicative C) (g := Multiplicative.ofAdd c)).symm)

theorem exists_inv {k m : ℕ} (h : Nat.Coprime k m) : ∃ a : ℤ, ∀ (U : Type) [AddCommGroup U] (u : U), m • u = 0 →
    a • k • u = u := by
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 h)
  refine ⟨a, fun U _ u hu => ?_⟩
  have : (a * k + b * m) • u = u := by rw [hab, one_smul]
  rwa [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, hu, smul_zero, add_zero] at this

theorem card_ker_eq {W U : Type} [AddCommGroup W] [AddCommGroup U] (Q G : W →ₗ[ℤ] W) (Q' : U →+ U) (ev : W →+ U)
    (k M ℓ : ℕ) (hk : Nat.Coprime k ℓ) (hk0 : k ≠ 0) (hM : M ≠ 0) (tf : ∀ (m : ℕ) (w : W), m ≠ 0 → m • w = 0 → w = 0)
    (hev : ∀ w, Q' (ev w) = ev (Q w)) (hGQ : ∀ w, G (Q w) = (k * M) • w) (hQG : ∀ w, Q (G w) = (k * M) • w)
    (hker : ∀ w, ev w = 0 ↔ ∃ b, w = M • b) (honto : ∀ u, M • u = 0 → ∃ w, ev w = u)
    (hQ' : ∀ u, Q' u = 0 → (k * M) • u = 0) :
    Nat.card {u : U // Q' u = 0 ∧ ∃ j : ℕ, ℓ ^ j • u = 0} =
      Nat.card {c : W ⧸ LinearMap.range Q // ∃ j : ℕ, ℓ ^ j • c = 0} := by
  have hM0 : ∀ w, ev (M • w) = 0 := fun w => (hker _).2 ⟨w, rfl⟩
  let φ : (W ⧸ LinearMap.range Q) →ₗ[ℤ] U := (LinearMap.range Q).liftQ (ev.toIntLinearMap ∘ₗ G) (by
    rintro _ ⟨w, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap]
    rw [hGQ, mul_comm, mul_smul, hM0])
  have hφ : ∀ w, φ (Submodule.Quotient.mk w) = ev (G w) := fun w => rfl
  have hφk : ∀ c, φ c = 0 → k • c = 0 := fun c hc => by
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨b, hb⟩ := (hker _).1 ((hφ w).symm.trans hc)
    have h1 : M • (k • w - Q b) = 0 := by
      rw [smul_sub, smul_smul, mul_comm, ← hQG, hb, map_nsmul, sub_self]
    have h2 := sub_eq_zero.1 (tf M _ hM h1)
    change (LinearMap.range Q).mkQ (k • w) = 0
    rw [h2]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨b, rfl⟩
  symm
  refine Nat.card_eq_of_bijective (fun c => ⟨φ c.1, ?_, ?_⟩) ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ c.1
    rw [← hw, hφ, hev, hQG, mul_comm, mul_smul, hM0]
  · obtain ⟨j, hj⟩ := c.2
    exact ⟨j, by rw [← map_nsmul, hj, map_zero]⟩
  · rintro ⟨c, i, hi⟩ ⟨d, j, hj⟩ h
    have h1 : φ (c - d) = 0 := by rw [map_sub]; exact sub_eq_zero.2 (congrArg Subtype.val h)
    obtain ⟨a, ha⟩ := exists_inv (hk.pow_right (i + j))
    have h2 := ha _ (c - d) (by
      rw [smul_sub, pow_add, mul_smul _ _ d, hj, mul_comm, mul_smul, hi, smul_zero, smul_zero, sub_zero])
    rw [hφk _ h1, smul_zero] at h2
    exact Subtype.ext (sub_eq_zero.1 h2.symm)
  · rintro ⟨u, hu, j, hj⟩
    obtain ⟨a, ha⟩ := exists_inv (hk.pow_right j)
    have h1 : M • u = 0 := by
      rw [← ha _ (M • u) (by rw [smul_comm, hj, smul_zero]), smul_smul k, hQ' u hu, smul_zero]
    obtain ⟨v, rfl⟩ := honto u h1
    obtain ⟨w, hw⟩ := (hker _).1 ((hev v).symm.trans hu)
    have h2 : M • (G w - k • v) = 0 := by
      rw [smul_sub, smul_smul, mul_comm, ← hGQ, hw, map_nsmul, sub_self]
    have h3 : φ (Submodule.Quotient.mk w) = k • ev v := by
      rw [hφ, sub_eq_zero.1 (tf M _ hM h2), map_nsmul]
    refine ⟨⟨a • k • a • Submodule.Quotient.mk w, j, ?_⟩, Subtype.ext ?_⟩
    · have h4 := hφk (ℓ ^ j • Submodule.Quotient.mk w) (by rw [map_nsmul, h3, smul_comm, hj, smul_zero])
      rw [smul_comm k a, smul_comm _ a, smul_comm _ a, smul_comm, smul_comm (ℓ ^ j) k, h4, smul_zero, smul_zero]
    · change φ _ = ev v
      rw [map_zsmul, map_nsmul, map_zsmul, h3, ha _ _ hj, ha _ _ hj]

theorem det_eq_of_intertwine {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module.Free ℤ A] [Module.Finite ℤ A]
    [Module.Free ℤ B] [Module.Finite ℤ B] (h : Module.finrank ℤ A = Module.finrank ℤ B) (f : A →ₗ[ℤ] A) (g : B →ₗ[ℤ] B)
    (i : A →ₗ[ℤ] B) (hi : Function.Injective i) (hc : g ∘ₗ i = i ∘ₗ f) : LinearMap.det g = LinearMap.det f := by
  let e : A ≃ₗ[ℤ] B := LinearEquiv.ofFinrankEq A B h
  have h0 : LinearMap.det (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) ≠ 0 := by
    intro h0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
    exact h0 (LinearMap.ker_eq_bot.2 (hi.comp e.symm.injective))
  have h1 : g ∘ₗ (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) =
      (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) ∘ₗ ((e : A →ₗ[ℤ] B) ∘ₗ f ∘ₗ (e.symm : B →ₗ[ℤ] A)) := by
    ext x
    simpa using LinearMap.congr_fun hc (e.symm x)
  have h2 := congrArg LinearMap.det h1
  rw [LinearMap.det_comp, LinearMap.det_comp (i ∘ₗ _), LinearMap.det_conj, mul_comm] at h2
  exact mul_left_cancel₀ h0 h2

section Mat
variable {O : Type} [CommRing O] {n : ℕ}

def mact (L : Type) [AddCommGroup L] [Module O L] (mu : Matrix (Fin n) (Fin n) O) : (Fin n → L) →ₗ[O] (Fin n → L) where
  toFun u i := ∑ j, mu i j • u j
  map_add' u v := by ext i; simp [Finset.sum_add_distrib]
  map_smul' a u := by ext i; simp [Finset.smul_sum, smul_comm a]

variable {L : Type} [AddCommGroup L] [Module O L]

theorem mact_apply (mu : Matrix (Fin n) (Fin n) O) (u : Fin n → L) (i : Fin n) : mact L mu u i = ∑ j, mu i j • u j := rfl

theorem mact_mul (a b : Matrix (Fin n) (Fin n) O) (u : Fin n → L) : mact L a (mact L b u) = mact L (a * b) u := by
  ext i
  simp only [mact_apply, Matrix.mul_apply, Finset.sum_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

theorem mact_nat (c : ℕ) (u : Fin n → L) : mact L ((c : O) • (1 : Matrix (Fin n) (Fin n) O)) u = c • u := by
  ext i
  simp only [mact_apply, Matrix.smul_apply, Matrix.one_apply, smul_ite, smul_zero, ite_smul, smul_one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Nat.cast_smul_eq_nsmul, smul_assoc, one_smul, Pi.smul_apply]

theorem det_mact [IsDomain O] [CharZero O] [Module.Free ℤ O] [Module.Finite ℤ O] [Module.Finite O L]
    [Module.Free ℤ L] (q : Matrix (Fin n) (Fin n) O) :
    LinearMap.det ((mact L q).restrictScalars ℤ) = Algebra.norm ℤ q.det ^ Module.finrank O L := by
  have : Module.Finite ℤ L := Module.Finite.trans O L
  obtain ⟨r, hr⟩ : ∃ r, r = Module.finrank O L := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := O) (M := L) hr.le
  rw [← hr]
  let f : (Fin r → Fin n → O) →ₗ[O] (Fin r → Fin n → O) :=
    LinearMap.pi fun s => (Matrix.toLin' q).comp (LinearMap.proj s)
  have hf : LinearMap.det f = q.det ^ r := by
    simp [f, LinearMap.det_pi]
  let i : (Fin r → Fin n → O) →ₗ[O] (Fin n → L) :=
    { toFun c j := ∑ s, c s j • v s
      map_add' c d := by ext j; simp [add_smul, Finset.sum_add_distrib]
      map_smul' a c := by ext j; simp [Finset.smul_sum, mul_smul] }
  have hi : Function.Injective i := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    ext s j
    have h1 : ∑ s, c s j • v s = 0 := congrFun hc j
    exact Fintype.linearIndependent_iff.1 hv (fun s => c s j) h1 s
  rw [det_eq_of_intertwine ?_ (f.restrictScalars ℤ) _ (i.restrictScalars ℤ) hi ?_, LinearMap.det_restrictScalars, hf,
    map_pow]
  · simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [finrank_int_eq_mul_of_finite (O := O) (M := L), ← hr]; ring
  · refine LinearMap.ext fun c => funext fun j => ?_
    change ∑ b, q j b • ∑ s, c s b • v s = ∑ s, (q.mulVec (c s) j) • v s
    simp only [Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm

theorem card_kills [IsDomain O] [CharZero O] [Module.Free ℤ O] [Module.Finite ℤ O] [Module.Finite O L]
    [Module.Free ℤ L] {P : Type} [AddCommGroup P] [Module O P] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (q g : Matrix (Fin n) (Fin n) O) (k M : ℕ) (hk : Nat.Coprime k ℓ) (hM : 0 < M)
    (hgq : g * q = ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O)) (ev : L →ₗ[O] P)
    (hker : ∀ a, ev a = 0 ↔ ∃ b, a = M • b) (honto : ∀ w : P, M • w = 0 → ∃ a, ev a = w) :
    Nat.card {u : Fin n → P // mact P q u = 0 ∧ ∃ j : ℕ, ℓ ^ j • u = 0} =
      ℓ ^ ((Algebra.norm ℤ q.det).natAbs ^ Module.finrank O L).factorization ℓ := by
  have : Module.Finite ℤ L := Module.Finite.trans O L
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hℓ.one_lt.ne' (by simpa using hk)
  have hc : k * M ≠ 0 := mul_ne_zero hk0 hM.ne'
  have tf : ∀ (m : ℕ) (w : Fin n → L), m ≠ 0 → m • w = 0 → w = 0 := fun m w hm h => by
    rw [← natCast_zsmul] at h
    exact (smul_eq_zero.1 h).resolve_left (by exact_mod_cast hm)
  have hGQ : ∀ w, mact L g (mact L q w) = (k * M) • w := fun w => by rw [mact_mul, hgq, mact_nat]
  have hdet : q.det ≠ 0 := by
    intro h
    have h1 := congrArg Matrix.det hgq
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hc) h1.symm
  have hqg : q * g = ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O) := by
    have h1 : (q * g - ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O)) * q = 0 := by
      rw [sub_mul, Matrix.mul_assoc, hgq]; simp
    have h2 := congrArg (· * q.adjugate) h1
    simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.zero_mul] at h2
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hdet)
  have hQG : ∀ w, mact L q (mact L g w) = (k * M) • w := fun w => by rw [mact_mul, hqg, mact_nat]
  have hinj : Function.Injective ((mact L q).restrictScalars ℤ) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    refine tf _ w hc ?_
    rw [← hGQ, show mact L q w = 0 from hw, map_zero]
  have hcard : Nat.card ((Fin n → L) ⧸ LinearMap.range ((mact L q).restrictScalars ℤ)) =
      (Algebra.norm ℤ q.det).natAbs ^ Module.finrank O L := by
    rw [← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _ hinj), ← Int.natAbs_pow, ← det_mact (L := L) q]
    congr 2
  have hfin : Finite ((Fin n → L) ⧸ LinearMap.range ((mact L q).restrictScalars ℤ)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact pow_ne_zero _ (Int.natAbs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 hdet))
  rw [← hcard, ← card_primary _ ℓ hℓ]
  refine card_ker_eq ((mact L q).restrictScalars ℤ) ((mact L g).restrictScalars ℤ) (mact P q).toAddMonoidHom
    (ev.compLeft (Fin n)).toAddMonoidHom k M ℓ hk hk0 hM.ne' tf (fun w => ?_) hGQ hQG (fun w => ?_) (fun u hu => ?_)
    (fun u hu => ?_)
  · ext i
    simp [mact_apply]
  · constructor
    · intro h
      choose b hb using fun i => (hker (w i)).1 (congrFun h i)
      exact ⟨b, funext hb⟩
    · rintro ⟨b, rfl⟩
      exact funext fun i => (hker _).2 ⟨b i, rfl⟩
  · choose a ha using fun i => honto (u i) (congrFun hu i)
    exact ⟨a, funext ha⟩
  · rw [← mact_nat (O := O), ← hgq, ← mact_mul, show mact P q u = 0 from hu, map_zero]
end Mat

end GlobalTheory.TorsCount

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

theorem card_kills_primary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (ℓ : ℕ), ℓ.Prime → ∀ (n : ℕ) (q g : Matrix (Fin n) (Fin n) (𝓞 E)) (k M : ℕ), Nat.Coprime k ℓ → 0 < M → g * q = ((k * M : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) → AllRat Xo x M → Nat.card {u : Fin n → (ptO Xo x ⟶ Xo.univ.t.G) // Kills Xo q u ∧ ∀ b, (∃ j : ℕ, u b ^ (ℓ ^ j) = 1)} = ℓ ^ ((Algebra.norm ℤ q.det).natAbs ^ (Dw.p + Dw.q)).factorization ℓ := by
  intro E _ _ _ H Dw l Xo K _ x ℓ hℓ n q g k M hk hM hgq hall
  obtain ⟨ev, hadd, hlin, hker, honto⟩ := ((_root_.GlobalTheory.torsion_rational_over_finite_extension E H Dw l Xo K x M hM).2 hall).2
  letI := ZPart.ptMod Xo (ptO Xo x)
  have := Dw.fin
  have := datum_free_int Dw
  let ev' : Dw.La →ₗ[𝓞 E] Additive (ptO Xo x ⟶ Xo.univ.t.G) :=
    { toFun a := Additive.ofMul (ev a)
      map_add' a b := congrArg Additive.ofMul (hadd a b)
      map_smul' o a := congrArg Additive.ofMul (hlin o a) }
  rw [← Dw.rank, ← TorsCount.card_kills ℓ hℓ q g k M hk hM hgq ev' (fun a => hker a) (fun w hw => honto w.toMul hw)]
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => Additive.ofMul) fun u => ?_)
  refine and_congr ((ZPart.kills_iff Xo q u).trans funext_iff.symm) ⟨fun h => ?_, fun ⟨j, hj⟩ b => ⟨j, congrFun hj b⟩⟩
  choose e he using h
  refine ⟨∑ b, e b, funext fun b => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
  change u b ^ (ℓ ^ ∑ b, e b) = 1
  rw [hd, pow_add, pow_mul, he, one_pow]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CdvrExtSt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PlaceExtField

theorem cdvrExtSt : PullbackSections.CDVRExtSt := by
  intro T hT K _ jK hfin
  letI := jK.toAlgebra
  obtain ⟨T', iT, e, ψ, _, he, hv, hψ, _, hres⟩ := exists_cdvr_finite_extension T K
  refine ⟨T', ψ.toRingHom, e, he, fun a _ => ?_, hres hT⟩

  have h : ψ.toRingHom (jK a) = iT a := hψ a
  rw [h, hv a]

end GlobalTheory.PlaceExtField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundOfColumnProductsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValue_bound_of_column_products : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ f : Fin n → PS T.Fr 1 (chD C.ch), (∀ b, IsIntPS T (f b)) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (∑ mo ∈ P.support, P.coeff mo * ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))) → ChBound C e ρ w n := by
  first | exact @GlobalTheory.PlaceInt.chBound_of_columns | exact GlobalTheory.PlaceInt.chBound_of_columns | (intros; apply GlobalTheory.PlaceInt.chBound_of_columns <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueChainRuleNormalizedPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt

theorem hv_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) (a : 𝓞 E) (N k k' : ℕ), a * H.bar a = (N : 𝓞 E) → k' = k * N → ∀ (n : ℕ) (F : Fin n → SecN Xo y.x k) (F' : Fin n → SecN Xo y.x k'), (∀ b, Pulls Xo a (F b) (F' b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → hv Xo c nab y k' F' P = algebraMap c.F S (nrm Dw c w a) * hv Xo c nab y k F P := by
  intro E _ _ _ H Dw l Xo c inst hstar nab hnab S _ _ y a N k k' haN hk n F F' hF w P hP
  have e : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star _ _ (fun x => (hstar x).trans rfl)
  subst e

  obtain ⟨⟨b, hbM⟩, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 c.F)) P.support
    (fun m => P.coeff m)
  have hb0 : algebraMap (𝓞 c.F) c.F b ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero hbM ((IsFractionRing.injective (𝓞 c.F) c.F) (by rw [h0, map_zero]))

  have hsmul : ∀ (k0 : ℕ) (G : Fin n → SecN Xo y.x k0),
      hv Xo c nab y k0 G (algebraMap (𝓞 c.F) c.F b • P) =
        algebraMap c.F S (algebraMap (𝓞 c.F) c.F b) * hv Xo c nab y k0 G P := by
    intro k0 G
    unfold hv
    rw [MvPolynomial.support_smul_eq hb0, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, _root_.mul_assoc]

  have hQ : algebraMap (𝓞 c.F) c.F b • P ∈ harmA c w n := by
    unfold HH HHa at hP
    obtain ⟨h1, h2, h3⟩ := hP
    refine ⟨⟨Submodule.smul_mem _ _ h1, fun σ i i' hi t => by rw [map_smul, h2 σ i i' hi t],
      fun m hm σ i => h3 m (MvPolynomial.support_smul hm) σ i⟩, fun m => ?_⟩
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hm : m ∈ P.support
    · obtain ⟨r, hr⟩ := hb m hm
      have hr' : algebraMap (𝓞 c.F) c.F r = algebraMap (𝓞 c.F) c.F b * P.coeff m := by
        rw [hr, Algebra.smul_def]
      rw [← hr']
      exact r.2
    · rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero]
      exact Subring.zero_mem _
  have key : hv Xo c nab y k' F' (algebraMap (𝓞 c.F) c.F b • P) =
      algebraMap c.F S (nrm Dw c w a) * hv Xo c nab y k F (algebraMap (𝓞 c.F) c.F b • P) :=
    GlobalTheory.T.harmonic_value_normalised_pullback_chain_rule E H Dw l Xo c nab hnab S y a N k (k' : ℤ) (by rw [hstar]; exact haN)
      (by exact_mod_cast hk) n F F' (fun i => hF i) w _ hQ
  rw [hsmul, hsmul, _root_.mul_left_comm] at key
  exact mul_left_cancel₀ ((map_ne_zero _).mpr hb0) key
end GlobalTheory.PlaceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueIntegralPointEqValueOnBiextensionCo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

def letterEquiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ) :
    Lt1 Dw × Fin n ≃ LtN Dw n where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun ℓ := (⟨ℓ.1, ℓ.2.1⟩, ℓ.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem toK_prod_evV (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] (K : Type) [CommRing K] [Algebra V K] {d n : ℕ}
    (f : Fin n → PS V 1 d) :
    FB.toK K (∏ b, evV (n := n) ![pt V d b] (f b)) =
      GlobalTheory.PowGerm.boxSer (fun b => MvPowerSeries.map (algebraMap V K) (f b)) := by
  have key : ∀ b : Fin n, evV (n := n) ![pt V d b] (f b) =
      MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) (f b) := by
    intro b
    have hX : ∀ j : Fin 1 × Fin d,
        MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d))
          (MvPowerSeries.X j : MvPowerSeries (Fin 1 × Fin d) V) =
        (fun p : Fin 1 × Fin d => (![pt V d b] : Fin 1 → Pt V n d) p.1 p.2) j := by
      rintro ⟨i, j⟩
      rw [Fin.fin_one_eq_zero i, MvPowerSeries.rename_X]
      simp [pt]
    show evC _ (f b) = _
    exact evC_eq_algHom _ (fun j => by
      have h := (hX j).symm
      simp only at h
      rw [h, MvPowerSeries.rename_X]
      simp) _ hX (f b)
  simp only [FB.toK, key, map_prod, GlobalTheory.PowGerm.boxSer, MvPowerSeries.rename_map]

theorem nabValN_boxSer_eq_chartVal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {S : Type} [Field S] [Algebra c.F S] [Algebra ℚ S]
    {y : FrPt Xo c S} (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (g : Fin n → PS S 1 C.d)
    (P : MvPolynomial (LtN Dw n) c.F) :
    chartVal C k g P = nabValN C.B S C.h H.w0 k (GlobalTheory.PowGerm.boxSer g) (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map (algebraMap c.F S) P) := by
  classical
  have hcc : MvPowerSeries.constantCoeff C.h = 0 := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h C.11
  have hcol : ∀ (m : LtN Dw n →₀ ℕ) (b : Fin n),
      ReciprocityTheory.ChartRestriction.G.TB.colM (Finsupp.mapDomain (letterEquiv Dw n).symm m) b = colOf m b := by
    intro m b
    unfold ReciprocityTheory.ChartRestriction.G.TB.colM colOf
    congr 1
    funext ℓ
    have hℓ : ((ℓ, b) : Lt1 Dw × Fin n) = (letterEquiv Dw n).symm ⟨ℓ.1, (ℓ.2, b)⟩ := rfl
    rw [hℓ, Finsupp.mapDomain_apply_of_injective (letterEquiv Dw n).symm.injective]
  have hP : MvPolynomial.map (algebraMap c.F S) P = MvPolynomial.rename (letterEquiv Dw n)
      (MvPolynomial.rename (letterEquiv Dw n).symm (MvPolynomial.map (algebraMap c.F S) P)) := by
    rw [MvPolynomial.rename_rename, Equiv.self_comp_symm, MvPolynomial.rename_id_apply]
  rw [hP, GlobalTheory.nabValN_boxSer S C.d (𝓞 E) C.B S C.h H.w0 hcc k n g (Lt1 Dw) (LtN Dw n) (letterEquiv Dw n)
    (fun ℓ => ℓ.2.2) C.uvec (fun ℓ => C.uvec ⟨ℓ.1, ℓ.2.1⟩) (fun _ => rfl) (fun _ => rfl),
    GlobalTheory.NabCol.sum_support_rename]
  unfold chartVal
  rw [MvPolynomial.support_map_of_injective _ (algebraMap c.F S).injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  simp only [hcol]

theorem hv_eq_nabValN : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → ∀ (k n : ℕ) (F : Fin n → SecN Xo (xOf y) k) (f : Fin n → PS T.V 1 (chD C.ch)), (∀ b, GermIs C k (F b) (f b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → letI := io.toAlgebra; hv Xo c nab y.1 k F P = nabValN B T.Fr (gaugeOf C) H.w0 k (FB.toK T.Fr (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b))) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C nab hnab B hB k n F f hF w P hP
  letI := io.toAlgebra
  obtain ⟨hG, hAct, -⟩ := hB
  have hgen := C.gen.1
  have hFK : B.FK T.Fr = C.ch.B.FK T.Fr := by
    unfold FB.FK FGLaw.mapF
    funext i
    simp [hG, hgen.1 i]
  have hAK : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    unfold FB.actK
    funext i
    simp [hAct, hgen.2.1 a i]
  have h1 := _root_.GlobalTheory.PlaceInt.hv_eq_chartVal E H Dw l Xo c hstar nab hnab T.Fr y.1 C.ch k n F
    (fun b => MvPowerSeries.map (algebraMap T.V T.Fr) (f b)) (fun b => hF b) w P hP
  rw [h1, nabValN_boxSer_eq_chartVal C.ch k _ P, ← toK_prod_evV T.V T.Fr f]
  exact GlobalTheory.ChartCmp.nabValN_congr_FK C.ch.B B T.Fr hFK hAK _ _ _ _ _ _ _

end GlobalTheory.PlaceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralChart_formalBiextension_gauge_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∃ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B ∧ ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → B.IsCanonGauge T.Fr (gaugeOf C) ∧ MvPowerSeries.constantCoeff (gaugeOf C) = 0 ∧ (letI := io.toAlgebra; (∀ (ℓ : Lt1 Dw) (a : 𝓞 E), (dAct T.Fr B a).mulVec (C.ch.uvec ℓ) = io (embK c ℓ.1 a) • C.ch.uvec ℓ) ∧ ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e ρ w n → ∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ g : PS T.V n (chD C.ch), ((-ρ : ℝ) : EReal) ≤ nval T.V e (nabValN B T.Fr (gaugeOf C) H.w0 k (FB.toK T.Fr g) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P)) := by
  first | exact @GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound | exact GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound | (intros; apply GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound <;> assumption)
end

