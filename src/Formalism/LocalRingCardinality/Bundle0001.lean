module

public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataLevel
public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

@[expose] public section

-- bundled from Formalism.LocalRingCardinality.ConjSqrtMinusD
section
namespace Formalism.BasicNotions

open NumberField

variable {R : Ranks}

theorem Host.sqrtMinusD_sq (H : Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem Host.conj_sqrtMinusD (H : Host R) : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h1 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) := H.conjE_apply H.φ₀ H.sqrtMinusD
  rw [h1, map_neg]
  set z := H.φ₀ H.sqrtMinusD
  have hz : z ^ 2 = -(H.d : ℂ) := by rw [← map_pow, H.sqrtMinusD_sq]; simp
  have hre : z.re = 0 := by
    have h2 := congrArg Complex.im hz
    have h3 := congrArg Complex.re hz
    simp [pow_two] at h2 h3
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
    rcases mul_eq_zero.mp (show z.re * z.im * 2 = 0 by linarith) with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · rw [h] at h3; nlinarith [sq_nonneg z.re]
    · norm_num at h
  apply Complex.ext <;> simp [hre]

theorem Host.exists_trace_one (H : Host R) : ∃ c : 𝓞 H.E, (c : H.E) + H.conj c = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.hyp.2.2.2.1; omega⟩
  set c : H.E := (1 + H.sqrtMinusD) / 2
  have hc : c ^ 2 - c + (m : H.E) = 0 := by
    have e : ((H.d : ℕ) : H.E) + 1 = 4 * (m : H.E) := by exact_mod_cast hm
    have hs := H.sqrtMinusD_sq
    simp only [c]
    linear_combination (1 / 4 : H.E) * hs - (1 / 4 : H.E) * e
  have hint : IsIntegral ℤ c := ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩
  refine ⟨⟨c, hint⟩, ?_⟩
  show c + H.conj c = 1
  simp only [c, map_div₀, map_add (f := _), map_one, H.conj_sqrtMinusD, map_ofNat]
  ring

end Formalism.BasicNotions
end

-- bundled from Formalism.LocalRingCardinality.DataBu
section
noncomputable section
namespace Formalism.BasicNotions
namespace Rows.Data
variable {R : Ranks} (D : Rows.Data R)

def iotaQ (μ : D.Tup) : D.Qsp μ →ₗ[ℂ] D.EE := (D.iota μ).domRestrict (D.Qsp μ)

theorem iotaQ_inj (μ : D.Tup) : Function.Injective (D.iotaQ μ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have hxQ : (x : D.Amb μ) ∈ D.V0 μ ⊓ (D.Usp μ)ᗮ := x.2
  have hU : (x : D.Amb μ) ∈ D.Usp μ := ⟨hxQ.1, hx⟩
  have h0 : inner ℂ (x : D.Amb μ) (x : D.Amb μ) = 0 := Submodule.inner_right_of_mem_orthogonal hU hxQ.2
  exact Subtype.ext (inner_self_eq_zero.mp h0)

def sec (μ : D.Tup) : D.EE →ₗ[ℂ] D.Amb μ :=
  (D.Qsp μ).subtype ∘ₗ (LinearEquiv.ofInjective (D.iotaQ μ) (D.iotaQ_inj μ)).symm.toLinearMap ∘ₗ
    ((LinearMap.range (D.iotaQ μ)).orthogonalProjectionOnto : D.EE →L[ℂ] LinearMap.range (D.iotaQ μ)).toLinearMap

theorem sec_iota (μ : D.Tup) (q : D.Amb μ) (hq : q ∈ D.Qsp μ) : D.sec μ (D.iota μ q) = q := by
  have hr : D.iota μ q ∈ LinearMap.range (D.iotaQ μ) := ⟨⟨q, hq⟩, rfl⟩
  have h1 : (LinearMap.range (D.iotaQ μ)).orthogonalProjectionOnto (D.iota μ q) = ⟨D.iota μ q, hr⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := LinearMap.range (D.iotaQ μ)) ⟨D.iota μ q, hr⟩
  have h2 : (LinearEquiv.ofInjective (D.iotaQ μ) (D.iotaQ_inj μ)) ⟨q, hq⟩ = ⟨D.iota μ q, hr⟩ := rfl
  simp only [sec, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, h1, ← h2, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.subtype_apply]

end Rows.Data

def Rows.BuDefQ {R : Ranks} (D : Rows.Data R) : Prop :=
  ∀ u (φ : D.Mu u) (x : D.EE), D.Bu u φ x = D.perCol u D.mu0 φ (D.sec D.mu0 x)

theorem D7.perCol_add (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (F G : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ (F + G) = D.what₂.perCol u D.what₂.mu0 φ F + D.what₂.perCol u D.what₂.mu0 φ G := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_add (f := _)]

theorem D7.perCol_zero (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) :
    D.what₂.perCol u D.what₂.mu0 φ 0 = 0 := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_zero]

end Formalism.BasicNotions
end
end

-- bundled from Formalism.LocalRingCardinality.DataGatTies
section
open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField

namespace Formalism.BasicNotions

structure GatTies (D : D7) where

  gat_k : ∀ u w h, (D.gat u w h).P.m + 1 = D.R.k

  gat_n : ∀ u w h (v : Fin (D.gat u w h).P.nV) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})] (σ : D.host.E ≃ₐ[ℚ] D.host.E), IsArithFrobAt ℤ σ P →
    (D.gat u w h).P.n' v = orderOf (D.host.galE σ).2

  gat_pos : ∀ u w h, (Σ v : Fin (D.gat u w h).P.nV, Fin ((D.gat u w h).P.n' v)) ≃ D.what₂.Tau

  gat_step : ∀ u w h (v : Fin (D.gat u w h).P.nV) (s : Fin ((D.gat u w h).P.n' v))
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E), IsArithFrobAt ℤ σ P →
    ((D.eTau (gat_pos u w h ⟨v, posAdd s 1⟩) : D.R.Psi) : D.R.GG) =
      ((D.eTau (gat_pos u w h ⟨v, s⟩) : D.R.Psi) : D.R.GG) *
        D.host.galE σ * D.R.cc

  gat_lam : ∀ u w h (v : Fin (D.gat u w h).P.nV) (s : Fin ((D.gat u w h).P.n' v))
    (i : Fin ((D.gat u w h).P.m + 1)),
    (D.gat u w h).P.lam0 v s i =
      ((D.fm u).lam 0 (gat_pos u w h ⟨v, s⟩)).w
        ⟨i.1, by have h1 := gat_k u w h; have h2 := i.2; simp only [Ranks.N]; omega⟩

end Formalism.BasicNotions
end

-- bundled from Formalism.LocalRingCardinality.DataLevelD
section
namespace Formalism.BasicNotions

def LevelData (D : D7) :=
  letI := D.host.cmStar
  ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)

end Formalism.BasicNotions
end

-- bundled from Formalism.LocalRingCardinality.DataMink
section
namespace Formalism.BasicNotions

abbrev minkM (n : ℕ) : ℕ := Formalism.HermitianLatticeCounting.S6.minkowskiM n

def DGamMink (D : D7) : Prop := (D.mem D.u₀).C.DGam = minkM (2 * D.R.f * D.R.N D.R.m)

end Formalism.BasicNotions
end

-- bundled from Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
section
noncomputable section

namespace Formalism.BasicNotions

open NumberField

theorem intCast_dvd_of_dvd_integers (E : Type) [Field E] [NumberField E] (a b : ℤ)
    (h : (b : 𝓞 E) ∣ (a : 𝓞 E)) : b ∣ a := by
  have h1 := map_dvd (Algebra.norm ℤ) h
  have ea : (a : 𝓞 E) = algebraMap ℤ (𝓞 E) a := by simp
  have eb : (b : 𝓞 E) = algebraMap ℤ (𝓞 E) b := by simp
  rw [ea, eb, Algebra.norm_algebraMap, Algebra.norm_algebraMap] at h1
  have hn : Module.finrank ℤ (𝓞 E) ≠ 0 := by
    rw [RingOfIntegers.rank]; exact (Module.finrank_pos).ne'
  exact (Int.pow_dvd_pow_iff hn).1 h1

theorem dvd_norm_sub_one (E : Type) [Field E] [NumberField E] (σ : E ≃ₐ[ℚ] E) (π : 𝓞 E) (T M : ℕ)
    (hT : (π : E) * σ (π : E) = (T : E)) (hπ : (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 E)}) :
    (M : ℤ) ∣ (T : ℤ) - 1 := by
  rw [Ideal.mem_span_singleton] at hπ
  obtain ⟨α, hα⟩ := hπ
  have hint : IsIntegral ℤ (σ (α : E)) := map_isIntegral_int σ (RingOfIntegers.isIntegral_coe α)
  set α' : 𝓞 E := ⟨σ (α : E), hint⟩ with hα'
  have e1 : (π : E) = 1 + (M : E) * (α : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) hα
    simp only [map_sub, map_one, map_mul, map_natCast] at this
    linear_combination this
  have e2 : σ (π : E) = 1 + (M : E) * (α' : E) := by
    have hc : (α' : E) = σ (α : E) := rfl
    rw [e1, hc]; simp
  have e3 : (T : E) - 1 = (M : E) * ((α : E) + (α' : E) + (M : E) * (α : E) * (α' : E)) := by
    rw [← hT, e2, e1]; ring
  have h5 : ((M : ℤ) : 𝓞 E) ∣ (((T : ℤ) - 1 : ℤ) : 𝓞 E) := by
    refine ⟨α + α' + (M : 𝓞 E) * α * α', ?_⟩
    apply RingOfIntegers.ext
    simp only [map_mul, map_add (f := _), map_natCast, map_intCast]
    push_cast
    exact e3
  exact intCast_dvd_of_dvd_integers E _ _ h5

namespace D7

variable (D : D7)

def modT : ℕ := D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2

theorem modT_dvd (u : D.what₂.Word) : (D.modT : ℤ) ∣ ((D.mem u).A.T : ℤ) - 1 := by
  obtain ⟨π, -, hT, hπ⟩ := D.T_norm u
  exact dvd_norm_sub_one D.host.E D.host.conj π _ _ hT hπ

theorem T_modEq (u : D.what₂.Word) : (D.mem u).A.T ≡ 1 [MOD D.modT] :=
  ((Nat.modEq_iff_dvd).2 (by exact_mod_cast D.modT_dvd u)).symm

theorem T_modEq_of_dvd (u : D.what₂.Word) {a : ℕ} (ha : a ∣ D.modT) : (D.mem u).A.T ≡ 1 [MOD a] :=
  (D.T_modEq u).of_dvd ha

theorem T_mod_of_dvd (u : D.what₂.Word) {a : ℕ} (ha : a ∣ D.modT) (h1 : 1 < a) : (D.mem u).A.T % a = 1 := by
  have h := D.T_modEq_of_dvd u ha
  rwa [Nat.ModEq, Nat.mod_eq_of_lt h1] at h

theorem g_dvd_modT (i : Fin 2) : D.host.g i ∣ D.modT := by
  have h : D.host.g i ∣ D.host.g 0 * D.host.g 1 := by
    fin_cases i
    · exact Dvd.intro _ rfl
    · exact Dvd.intro_left _ rfl
  exact Dvd.dvd.mul_left (dvd_pow h two_ne_zero) _

theorem gg_dvd_modT : (D.host.g 0 * D.host.g 1) ^ 2 ∣ D.modT := Dvd.intro_left _ rfl

theorem cond_dvd_modT : D.host.QS * D.host.q * D.host.d ∣ D.modT := Dvd.intro _ rfl

theorem q_prime : D.host.q.Prime := D.host.hyp.1

theorem d_prime : D.host.d.Prime := D.host.hyp.2.1

theorem one_lt_cond : 1 < D.host.QS * D.host.q * D.host.d := by
  have h1 := D.host.QS_pos
  have h2 := D.q_prime.pos
  have h3 := D.d_prime.two_le
  have : 1 * 1 * 2 ≤ D.host.QS * D.host.q * D.host.d := by gcongr <;> omega
  omega

theorem T_mod_g (u : D.what₂.Word) (i : Fin 2) : (D.mem u).A.T % D.host.g i = 1 :=
  D.T_mod_of_dvd u (D.g_dvd_modT i) (D.host.g_prime i).one_lt

theorem T_mod_gg (u : D.what₂.Word) : (D.mem u).A.T % (D.host.g 0 * D.host.g 1) ^ 2 = 1 := by
  refine D.T_mod_of_dvd u D.gg_dvd_modT ?_
  have h0 := (D.host.g_prime 0).two_le
  have h1 := (D.host.g_prime 1).two_le
  have : 2 * 2 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_le_mul h0 h1
  nlinarith

theorem T_mod_cond (u : D.what₂.Word) : (D.mem u).A.T % (D.host.QS * D.host.q * D.host.d) = 1 :=
  D.T_mod_of_dvd u D.cond_dvd_modT D.one_lt_cond

private theorem tower_dvd_modT : 2 ^ (D.R.e + 2) ∣ D.modT :=
  D.host.tower_dvd.trans (dvd_trans ⟨D.host.q * D.host.d, by ring⟩ D.cond_dvd_modT)

theorem T_mod_four (u : D.what₂.Word) : (D.mem u).A.T % 4 = 1 :=
  D.T_mod_of_dvd u (dvd_trans ⟨2 ^ D.R.e, by ring⟩ (tower_dvd_modT D)) (by norm_num)

theorem T_mod_q (u : D.what₂.Word) : (D.mem u).A.T % D.host.q = 1 :=
  D.T_mod_of_dvd u (dvd_trans ⟨D.host.QS * D.host.d, by ring⟩ D.cond_dvd_modT) D.q_prime.one_lt

theorem T_mod_d (u : D.what₂.Word) : (D.mem u).A.T % D.host.d = 1 :=
  D.T_mod_of_dvd u (dvd_trans ⟨D.host.QS * D.host.q, by ring⟩ D.cond_dvd_modT) D.d_prime.one_lt

theorem T_ne_g (u : D.what₂.Word) (i : Fin 2) : (D.mem u).A.T ≠ D.host.g i := by
  intro h
  have h1 := D.T_mod_g u i
  rw [h, Nat.mod_self] at h1
  exact zero_ne_one h1

theorem T_ne_two (u : D.what₂.Word) : (D.mem u).A.T ≠ 2 := by
  have h1 := D.T_mod_four u
  omega

theorem T_ne_q (u : D.what₂.Word) : (D.mem u).A.T ≠ D.host.q := by
  intro h
  have h1 := D.T_mod_q u
  rw [h, Nat.mod_self] at h1
  exact zero_ne_one h1

theorem T_ne_d (u : D.what₂.Word) : (D.mem u).A.T ≠ D.host.d := by
  intro h
  have h1 := D.T_mod_d u
  rw [h, Nat.mod_self] at h1
  exact zero_ne_one h1

end D7

end Formalism.BasicNotions

end
end

