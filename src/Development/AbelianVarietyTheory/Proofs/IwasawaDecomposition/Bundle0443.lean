module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
public import Formalism.LocalToGlobal.Columns.Bundle0013
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalMoveClassRepIffLocalConditions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.UnipotentAdelicQuotients.Bundle0002
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0032
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimePrimesNotOverBadPrimePlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

theorem vT_notOver_SBof : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (v : HeightOneSpectrum (𝓞 B.host.F)), Formalism.L2.Col.IsOver v P.1 → ∀ (u : B.Word), ∀ P' ∈ (B.primes X).vT u, ¬ Formalism.L2.Col.IsOver v P' := by
  intro B X I hI a P v hP u P' hP' hv'
  have hok := (GlobalTheory.BasePrimes.primes_ok B X).1
  have hT : ((B.primes X).T u : 𝓞 B.fields.E) ∉ P.1.asIdeal :=
    GlobalTheory.MuOffMove.level_notMem_rowSG hok hI.sel_ok (hI.T_mem u) P.2
  have hpi : (B.primes X).piT u ∈ P'.asIdeal := Formalism.L2.Col.decoFin_mem_of_mem_divs hP'
  have hTP' : ((B.primes X).T u : 𝓞 B.fields.E) ∈ P'.asIdeal := by
    rw [← hok.piT_norm u]
    exact Ideal.mul_mem_right _ _ hpi
  rcases Formalism.L2.Col.rll_over_cases B.sp.cm hP hv' with h | h
  · subst h
    exact hT hTP'
  · subst h
    rw [Formalism.L2.Col.mem_conjP, map_natCast] at hTP'
    exact hT hTP'

end GlobalTheory.Mem.Col2.AdT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConstantWeilCharacterValuesIsIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT


open Classical in
theorem addChar_isIntegral {A : Type} [AddCommGroup A] [Finite A] {K : Type} [Field K] (ψ : AddChar A K) (y : A) :
    IsIntegral ℤ (ψ y) := by
  refine IsIntegral.of_pow (Nat.card_pos (α := A)) ?_
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  exact isIntegral_one

theorem qOf_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : 0 < qOf w := by
  refine Nat.pos_of_ne_zero ?_
  unfold qOf
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact w.ne_bot

theorem ciPsi_isIntegral {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
    (P : SB) (x : X.E) : IsIntegral ℤ (ciPsi Ch P x) := by
  classical
  unfold ciPsi
  split
  · have := ciFinite (X := X) (qOf_pos P.1).ne'
    exact addChar_isIntegral _ _
  · exact isIntegral_one

theorem twZeta_pow_eq_one {X : Fields} (σ₀ : X.K →+* ℂ) {N : ℕ} (hN : 0 < N)
    (hex : ∃ z : X.K, σ₀ z = Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))) : twZeta σ₀ N ^ N = 1 := by
  have hs : σ₀ (twZeta σ₀ N) = Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) := Classical.epsilon_spec hex
  apply σ₀.injective
  rw [map_pow, hs, map_one, ← Complex.exp_nat_mul]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show (N : ℂ) * (2 * Real.pi * Complex.I / (N : ℂ)) = 2 * Real.pi * Complex.I by field_simp]
  exact Complex.exp_two_pi_mul_I

theorem twPsiQ_isIntegral {X : Fields} (σ₀ : X.K →+* ℂ) (xi0 : X.E) (P : HeightOneSpectrum (𝓞 X.E)) (D : ℕ)
    (hz : twZeta σ₀ (qOf P ^ D) ^ (qOf P ^ D) = 1) (a : X.E) : IsIntegral ℤ (twPsiQ σ₀ xi0 P D a) := by
  classical
  unfold twPsiQ
  split
  · refine IsIntegral.of_pow (pow_pos (qOf_pos P) D) ?_
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hz, _root_.one_zpow]
    exact isIntegral_one
  · exact isIntegral_one

theorem psi_isIntegral : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (a : I.ι) (P : SBof I a) (x : B.fields.E),
    IsIntegral ℤ ((I.cst a).psi P x) := by
  intro B X I h ht a P x
  rw [ht.cst_eq a]
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · rw [twCst_psi_g hP]
    exact ciPsi_isIntegral _ _ _
  · rw [twCst_psi_Q hP]
    exact twPsiQ_isIntegral _ _ _ _
      (twZeta_pow_eq_one _ (pow_pos (qOf_pos P.1) _) (TC.root_of_ok h ht.deep a P hP)) x

end GlobalTheory.Mem.Col2.AdT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchTupleChartMemberChart
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

set_option maxHeartbeats 2000000 in
theorem match_idx : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))) (i : ℕ), i ≤ B.R.m → 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∃ (c0f : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → (I.stp u I.mu0 i).Cl) (t : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), (∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (t β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) ∧ (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (t β) = 1) ∧ (a = I.mu0 → ∀ β, t β = 1) ∧ ∀ β, ∃ c, GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β ∧ ∀ s : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) s = 1) → (∀ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((t β)⁻¹ * s * t β) κ → ∃ κ0, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u I.mu0 i (c0f β) s κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr (c0f β).1 κ0) ∧ (∀ κ0, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u I.mu0 i (c0f β) s κ0 → ∃ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((t β)⁻¹ * s * t β) κ) := by
  intro B X I hI _hP l u a Q i hi h1 hm hQ
  by_cases ha : a = I.mu0
  · subst ha
    haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
    refine ⟨fun β => β.2.choose, fun _ => 1, fun _ => ⟨DecoF.base _ _ _ _ _, isPtOf_base _, rfl⟩,
      fun _ _ _ => map_one _, fun _ _ => rfl, fun β => ⟨β.2.choose, Subtype.ext β.2.choose_spec, fun s _ => ?_⟩⟩
    simp only [inv_one, one_mul, mul_one]
    exact ⟨fun κ hκ => ⟨κ, hκ, rfl⟩, fun κ0 hκ0 => ⟨κ0, hκ0⟩⟩
  · have key : ∀ β : Chart I u a i, ∃ (c0 : (I.stp u I.mu0 i).Cl) (t : GA B (B.R.N i)),
        (∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf t p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) ∧
        (∀ (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) →
          bc (prV (E := B.host.E) v) t = 1) ∧
        ∃ c, chartOf I u a i c = β ∧ ∀ s : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) s = 1) →
          (∀ κ, LocMv I u a i c (t⁻¹ * s * t) κ → ∃ κ0, LocMv I u I.mu0 i c0 s κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr c0.1 κ0) ∧
          (∀ κ0, LocMv I u I.mu0 i c0 s κ0 → ∃ κ, LocMv I u a i c (t⁻¹ * s * t) κ) := by
      intro β
      obtain ⟨b0, x', hx1', hxg', hxc'⟩ := GlobalTheory.T.exists_conj_referenceChartIndex I hI l a i h1 hm (β.2.choose).1
      obtain ⟨c0, rfl, y, hy, hcos⟩ := GlobalTheory.T.exists_reference_class_matching_coupling_coset I hI l u a i h1 hm β.2.choose b0
      let x : ∀ w : (B.primes X).vGs, GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ w.1.asIdeal) := fun w => y w * x' w
      have hx1 : i + 1 = B.R.m → ∀ w, x w = y w := fun h w => by simp [x, hx1' h w]
      have hconj : ∀ g : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs), (fun w => x w * g w * (x w)⁻¹) =
          y * (fun w => x' w * g w * (x' w)⁻¹ : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs)) * y⁻¹ := fun g => by
        funext w
        show y w * x' w * g w * (y w * x' w)⁻¹ = y w * (x' w * g w * (x' w)⁻¹) * (y w)⁻¹
        group
      have hxg : ∀ g : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs), g ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).grp ↔
          (fun w => x w * g w * (x w)⁻¹) ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).grp := fun g => by
        rw [hxg' g, hconj g]
        constructor
        · intro h
          exact mul_mem (mul_mem hy h) (inv_mem hy)
        · intro h
          have h2 := mul_mem (mul_mem (inv_mem hy) h) hy
          simpa [mul_assoc] using h2
      have hxc : ∀ (g : ↥(levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).grp) (g0 : ↥(levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).grp),
          (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) →
          (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).chr g = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).chr g0 := fun g g0 h => by
        have hm' := (hxg' g.1).1 g.2
        rw [hxc' g ⟨_, hm'⟩ (fun w => rfl)]
        have : g0 = ⟨y, hy⟩ * ⟨_, hm'⟩ * (⟨y, hy⟩)⁻¹ := Subtype.ext ((funext h).trans (hconj g.1))
        rw [this, map_mul, map_mul, map_inv, mul_comm (_ * _), ← mul_assoc, inv_mul_cancel, one_mul]
      obtain ⟨t, ht_std, ht_off, ht_res⟩ := GlobalTheory.T.exists_unitaryAdelic_lift_typePrime_reductions I hI l u (B.R.N i) x
      refine ⟨c0, t, ht_std, ht_off, β.2.choose, Subtype.ext β.2.choose_spec, fun s hs => ⟨?_, ?_⟩⟩
      · intro κ hκ
        obtain ⟨hg, hco, hC0, hCQ⟩ := (_root_.GlobalTheory.Mem.Col2.TC.ChTw.Match.locMv_iff I hI u a i hi _ _ κ).1 hκ
        rw [GlobalTheory.T.localConditions_conj_unitary_keepsStdLattice I hI l u (B.R.N i) t s x _ ht_std (fun v hv => ht_off v (Or.inl hv)) ht_res] at hC0
        have hθ : κ.2.2 = 1 := Subtype.ext ((GlobalTheory.T.twistLocalCondition_conj_iff_frameChange_trivial I hI l u a Q hQ (B.R.N i) t s _ ht_off hs).1 hCQ)
        have hmem := (hxg κ.2.1.1).1 κ.2.1.2
        let κ0 : (I.stp u I.mu0 i).G c0.1 := (1, ⟨_, hmem⟩, 1)
        have hg0 : (I.stp u I.mu0 i).gam c0.1 κ0 = 1 := by
          show ufGL B.fields.E (B.R.N i) 1 = 1
          exact map_one _
        refine ⟨κ0, (_root_.GlobalTheory.Mem.Col2.TC.ChTw.Match.locMv_iff I hI u I.mu0 i hi _ _ κ0).2 ⟨hg0, ?_, hC0, ?_⟩, ?_⟩
        · refine (hcos κ κ0 hg hg0 hθ fun h => ?_).1 hco
          intro w
          show x w * κ.2.1.1 w * (x w)⁻¹ = y w * κ.2.1.1 w * (y w)⁻¹
          rw [hx1 h w]
        · intro P
          have h0 : P.1 ∈ (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) := ColIn.twistPrimes_reference_tuple_eq_empty I ▸ P.2
          simp at h0
        · have ea : (I.stp u a i).chr (β.2.choose).1 κ = (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).chr κ.2.1 *
              (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).chr κ.2.2 := rfl
          have e0 : (I.stp u I.mu0 i).chr c0.1 κ0 = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).chr κ0.2.1 *
              (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i c0.1).chr 1 := rfl
          refine ea.trans (Eq.trans ?_ e0.symm)
          rw [hθ, map_one, map_one, mul_one, mul_one]
          exact hxc κ.2.1 κ0.2.1 fun w => rfl
      · intro κ0 hκ0
        obtain ⟨hg, hco, hC0, -⟩ := (_root_.GlobalTheory.Mem.Col2.TC.ChTw.Match.locMv_iff I hI u I.mu0 i hi _ _ κ0).1 hκ0
        have hmem : (fun w => (x w)⁻¹ * κ0.2.1.1 w * x w) ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i (β.2.choose).1).grp := by
          have e1 : (fun w => x w * ((x w)⁻¹ * κ0.2.1.1 w * x w) * (x w)⁻¹) = κ0.2.1.1 := funext fun w => by group
          refine (hxg _).2 ?_
          rw [e1]
          exact κ0.2.1.2
        let κ : (I.stp u a i).G (β.2.choose).1 := (1, ⟨_, hmem⟩, 1)
        have hgk : (I.stp u a i).gam (β.2.choose).1 κ = 1 := by
          show ufGL B.fields.E (B.R.N i) 1 = 1
          exact map_one _
        have e : (fun w => x w * κ.2.1.1 w * (x w)⁻¹) = κ0.2.1.1 := by
          funext w
          show x w * ((x w)⁻¹ * κ0.2.1.1 w * x w) * (x w)⁻¹ = κ0.2.1.1 w
          group
        refine ⟨κ, (_root_.GlobalTheory.Mem.Col2.TC.ChTw.Match.locMv_iff I hI u a i hi _ _ κ).2 ⟨hgk, ?_, ?_, ?_⟩⟩
        · refine (hcos κ κ0 hgk hg rfl fun h => ?_).2 hco
          intro w
          show κ0.2.1.1 w = y w * ((x w)⁻¹ * κ0.2.1.1 w * x w) * (y w)⁻¹
          rw [hx1 h w]
          group
        · rw [GlobalTheory.T.localConditions_conj_unitary_keepsStdLattice I hI l u (B.R.N i) t s x _ ht_std (fun v hv => ht_off v (Or.inl hv)) ht_res, e]
          exact hC0
        · exact (GlobalTheory.T.twistLocalCondition_conj_iff_frameChange_trivial I hI l u a Q hQ (B.R.N i) t s _ ht_off hs).2 rfl
    exact ⟨fun β => (key β).choose, fun β => (key β).choose_spec.choose, fun β => (key β).choose_spec.choose_spec.1,
      fun β => (key β).choose_spec.choose_spec.2.1, fun h => absurd h ha, fun β => (key β).choose_spec.choose_spec.2.2⟩

end GlobalTheory.Mem.Col2.TC.ChTw.Match
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLocalizedWeylLatticeIffDetTwistedEval
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LocDictT

theorem eval_map_actP {K S ι : Type} [Field K] [CommRing S] [Fintype ι] {n : ℕ} (φ : K →+* S)
    (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (P : Pol K ι n) (y : ι → Matrix (Fin n) (Fin n) S) :
    MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (MvPolynomial.map φ (actP lam g P)) =
      φ (detTwK lam g) * MvPolynomial.eval (fun k : ι × Fin n × Fin n =>
        (((((g k.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ) * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ P) := by
  have key : ((MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2)).comp
      ((MvPolynomial.map φ).comp (trAct g).toRingHom)) =
      (MvPolynomial.eval (fun k : ι × Fin n × Fin n =>
        (((((g k.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ) * y k.1) k.2.1 k.2.2)).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, Formalism.GradedWeylDivisibility.blockAct, Matrix.mul_apply]
  unfold actP
  rw [LinearMap.smul_apply, MvPolynomial.smul_eq_C_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C]
  congr 1
  exact RingHom.congr_fun key P

theorem invTr_bc_inv_transpose {E K : Type} [Field E] [Field K] {n : ℕ} (φ : E →+* K) (Bm : GL (Fin n) E) :
    ((((inside₂ K n (bc φ Bm))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ = (Bm : Matrix (Fin n) (Fin n) E).map φ := by
  rfl

theorem iL_emb {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (Pl : Examples₂.EntPl (I.rec7 l Z)) (w : (I.rec7 l Z).what₂.places.Pl) (τ : (I.rec7 l Z).what₂.Tau) (x : B.fields.E) :
    Pl.iL w (B.fields.emb τ x) = TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ x := by
  refine (Pl.iL_lam w (B.fields.emb τ x)).trans ?_
  have h : TaylorLogMetric.embT (I.rec7 l Z) τ x = B.embLL (B.fields.emb τ x) := by
    rw [GlobalTheory.Pdv.FormsStd.embT_eq I l Z]
    rfl
  unfold TaylorLogMetric.tauEmb
  rw [h]
  rfl

theorem detPow_map {K S : Type} [Field K] [Field S] {n : ℕ} (φ : K →+* S) (g : GL (Fin n) K) (e : ℤ) :
    φ (detPow K n g e) = ((((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ).map φ).det ^ e := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  congr 1
  show φ (g : Matrix (Fin n) (Fin n) K).det = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_transpose]
  rfl

theorem atBas_apply {D : D7} (P : Examples₂.EntPl D) (w : D.what₂.places.Pl) {N : ℕ}
    (M : D.what₂.Tau → Matrix (Fin N) (Fin N) (Cw D w)) (Q : MvPolynomial (GL3Theta.FrV D N) D.what₂.LL) (y : FrP D w N) :
    atBas P w M Q y = MvPolynomial.eval (fun k : GL3Theta.FrV D N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map (P.iL w) Q) := rfl

theorem final_eq {S T LL : Type} [Field S] [CommRing LL] [Fintype T] {N : ℕ} (φ : LL →+* S)
    (P : MvPolynomial (T × Fin N × Fin N) LL) (A g M y : T → Matrix (Fin N) (Fin N) S) (e : T → ℤ)
    (hM : ∀ τ, M τ = A τ * g τ) :
    (∏ τ, (g τ).det ^ e τ) * ((∏ τ, (A τ).det ^ e τ) *
      MvPolynomial.eval (fun k : T × Fin N × Fin N => (A k.1 * (g k.1 * y k.1)) k.2.1 k.2.2) (MvPolynomial.map φ P)) =
    (∏ τ, (M τ).det ^ e τ) * MvPolynomial.eval (fun k : T × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ P) := by
  simp only [hM, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_assoc]
  ring

theorem detTwisted_polyEval_mul_factor_eq_of_eq {S T LL : Type} [Field S] [CommRing LL] [Fintype T] {N : ℕ} (φ : LL →+* S)
    (P : MvPolynomial (T × Fin N × Fin N) LL) (A G g M y : T → Matrix (Fin N) (Fin N) S) (e e' : T → ℤ)
    (hA : ∀ τ, G τ = A τ) (he : ∀ τ, e' τ = e τ) (hM : ∀ τ, M τ = A τ * g τ) :
    (∏ τ, (g τ).det ^ e τ) * ((∏ τ, (A τ).det ^ e' τ) *
      MvPolynomial.eval (fun k : T × Fin N × Fin N => (G k.1 * (g k.1 * y k.1)) k.2.1 k.2.2) (MvPolynomial.map φ P)) =
    (∏ τ, (M τ).det ^ e τ) * MvPolynomial.eval (fun k : T × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ P) := by
  have h1 : G = A := funext hA
  have h2 : e' = e := funext he
  subst h1 h2
  exact final_eq φ P G g M y e' hM


set_option maxHeartbeats 1000000 in
theorem mem_locW_iff_delW : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : (I.stp u μ (i + 1)).Cl) (z : VV B.LL (lamT (B.hcW u) (i + 1))), (z ∈ locW B.places w (delAtr B.fields.emb (lamT (B.hcW u) (i + 1)) ((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c'))) ↔ (fun y => (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) * atBas Pl w (Bs u μ w (i + 1) c') (show MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N (i + 1))) (I.rec7 l Z).what₂.LL from z.1) y) ∈ WeylLatticeDuality.DelW ((I.rec7 l Z).what₂.places.resChar w) (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N (i + 1)) (extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i))) := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hLF i hi c' z
  obtain ⟨hlat, hloc⟩ := _root_.GlobalTheory.LshOffLevel.lsh_lattice_and_loc_eq I hOk hPins l Z Y u μ w hLF (i + 1) hi c'
  haveI : Fact (B.places.resChar w).Prime := ⟨B.places.resChar_prime w⟩
  have hspanN : Submodule.span B.fields.E
      (((I.stp u μ (i + 1)).rep c').1.1.deco.1.N : Set (Fin (B.R.N (i + 1)) → B.fields.E)) = ⊤ := by
    open Formalism.HermitianLatticesTheory Module in
    let L := ((I.stp u μ (i + 1)).rep c').1.1.deco.1.N
    have hL := ((I.stp u μ (i + 1)).rep c').1.1.deco.2.lat
    have hu : IsUnimodular (Formalism.L2.Col.hStd B.fields.E (B.R.N (i + 1))) L :=
      ((I.stp u μ (i + 1)).rep c').1.1.deco.2.uni
    let W := Submodule.span B.fields.E (L : Set (Sp B.fields.E (B.R.N (i + 1))))
    change W = ⊤
    by_contra h
    let e : Sp B.fields.E (B.R.N (i + 1)) ≃ₗ⋆[B.fields.E] Sp B.fields.E (B.R.N (i + 1)) := starLinearEquiv B.fields.E
    let g : Sp B.fields.E (B.R.N (i + 1)) →ₗ[B.fields.E] Module.Dual B.fields.E W :=
      (LinearMap.domRestrict' W).comp ((Formalism.L2.Col.hStd B.fields.E (B.R.N (i + 1))).comp e.toLinearMap)
    have hdim : finrank B.fields.E (Module.Dual B.fields.E W) <
        finrank B.fields.E (Sp B.fields.E (B.R.N (i + 1))) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : B.fields.E) : a • e x ∈ L := by
      rw [← hu, dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : Formalism.L2.Col.hStd B.fields.E (B.R.N (i + 1)) (e x) y = 0 :=
        congrArg (fun f : Module.Dual B.fields.E W => f ⟨y, Submodule.subset_span hy⟩)
          (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let j : B.fields.E →ₗ[𝓞 B.fields.E] L :=
      ((LinearMap.toSpanSingleton B.fields.E _ (e x)).restrictScalars (𝓞 B.fields.E)).codRestrict L hsmul
    let : Module.Finite (𝓞 B.fields.E) L := Module.Finite.iff_fg.mpr hL.fg
    let : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.Finite.of_injective j fun a b hab =>
      smul_left_injective B.fields.E (fun hz => hx₀ (e.map_eq_zero_iff.mp hz)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField B.fields.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E))
  have hfull : Submodule.IsFullLattice B.fields.E
      ((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c')) := by
    letI := hlat
    refine ⟨?_⟩
    apply top_unique
    rw [← hspanN]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨s, hs, hmem⟩ := (hloc x).mpr ⟨1, by simpa using ((I.rec7 l Z).what₂.places.resChar_prime w).ne_one, by simpa using hx⟩
    have hs0 : (s : B.fields.E) ≠ 0 := by
      intro hz
      have : s = 0 := Nat.cast_eq_zero.mp hz
      subst s
      exact hs (dvd_zero _)
    have hm : (s : B.fields.E) • x ∈ Submodule.span B.fields.E
        (((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c')) : Set _) := Submodule.subset_span hmem
    have := (Submodule.span B.fields.E
      (((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c')) : Set (Fin (B.R.N (i + 1)) → B.fields.E))).smul_mem (s : B.fields.E)⁻¹ hm
    simpa [smul_smul, hs0] using this
  obtain ⟨Bm, hBm0⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (B.places.resChar w) B.fields.E _
    ((I.stp u μ (i + 1)).rep c').1.1.deco.2.lat.fg hspanN
  have hBm : Formalism.L2.Forms.IsLocBasis (B.places.resChar w) (((I.stp u μ (i + 1)).Lsh c'.1 ((I.stp u μ (i + 1)).rep c')) : Set _) Bm := by
    intro x
    exact (hloc x).trans (hBm0 x)
  have hBmN : Formalism.L2.Forms.IsLocBasis (B.places.resChar w) (((O u μ).lat (i + 1) c').1 : Set (Fin ((I.rec7 l Z).R.N (i + 1)) → (I.rec7 l Z).host.E)) Bm := by
    intro x
    rw [hStd.lat u μ (i + 1) c']
    exact (hloc x).symm.trans (hBm x)
  rw [GlobalTheory.WeylLocOnePlace.mem_locW_delAtr_iff B.fields.emb B.embLL B.places (I.rec7 l Z).plEq
    (fun w x hx => (I.rec7 l Z).val_eq w x hx)
    (lamT (B.hcW u) (i + 1)) (lamT (B.hcW u) (i + 1)) (fun _ => rfl) _ hfull w Bm hBm z]
  rw [_root_.GlobalTheory.Mem.IntSpanDelW.map_mem_vlIntSpan_iff_delW B.embLL B.places w (Pl.iL w) (Pl.iL_int w) (lamT (B.hcW u) (i + 1)) _
    (((rhoVr B.fields.emb (lamT (B.hcW u) (i + 1))) Bm⁻¹) z).2]
  obtain ⟨n, hw, hn, hnat, hds⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ ((I.tw l l0 Z).fm u μ) i hi
  have hlam := GlobalTheory.Pdv.FormsStd.lamTG_eq I l Z l0 u μ
  have e : (fun τ => (lamT (B.hcW u) (i + 1) τ).natW) = extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i) := by
    funext τ r
    rw [← hlam]
    refine (hnat τ r).trans ?_
    congr 1
    funext τ' r'
    exact hw τ' r'
  have eds : ∀ τ, (lamT (B.hcW u) (i + 1) τ).detShift = -((I.rec7 l Z).chTw u μ).sDiv i τ := fun τ => by
    rw [← hlam]
    exact hds τ
  rw [e]
  choose g hg1 hg2 hg3 using fun τ => _root_.GlobalTheory.LocBasisBasR.main (I.rec7 l Z) (Pl.lam w) τ _ Bm (Bs u μ w (i + 1) c' τ) hBmN
    (hBas u μ w (i + 1) hi c' τ)
  refine (_root_.GlobalTheory.DelWSub.delW_rowSub _ _ _ _ g (∏ τ, (g τ).det ^ (-((I.rec7 l Z).chTw u μ).sDiv i τ)) hg1 hg2 ?_ _).trans ?_
  · rw [norm_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [norm_zpow, hg2, _root_.one_zpow]
  · apply iff_of_eq
    congr 1
    funext y
    have hM : ∀ τ, ((((vlBdF B.fields.emb fun _ => Bm)⁻¹ τ : GL (Fin (B.R.N (i + 1))) B.LL) :
        Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.LL)ᵀ).map (Pl.iL w) =
        (Bm : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E).map (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ) := by
      intro τ
      rw [show (vlBdF B.fields.emb fun _ => Bm)⁻¹ τ = (inside₂ _ _ (bc (B.fields.emb τ) Bm))⁻¹ from rfl,
        invTr_bc_inv_transpose]
      ext a b
      exact iL_emb I l Z Pl w τ _
    have hdet : Pl.iL w (detTwK (lamT (B.hcW u) (i + 1)) (vlBdF B.fields.emb fun _ => Bm)⁻¹) =
        ∏ τ, ((Bm : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E).map
          (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ)).det ^ (lamT (B.hcW u) (i + 1) τ).detShift := by
      unfold detTwK
      rw [map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [detPow_map]
      exact congrArg (fun M => Matrix.det M ^ (lamT (B.hcW u) (i + 1) τ).detShift) (hM τ)
    beta_reduce
    rw [GlobalTheory.WeylLocOnePlace.rhoVr_inv_coe]
    have hev := eval_map_actP (Pl.iL w) (lamT (B.hcW u) (i + 1)) (vlBdF B.fields.emb fun _ => Bm)⁻¹ z.1 (fun τ => g τ * y τ)
    beta_reduce at hev
    erw [hev]
    erw [atBas_apply, hdet]
    exact detTwisted_polyEval_mul_factor_eq_of_eq (Pl.iL w) z.1
      (fun τ => (Bm : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E).map (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ))
      (fun τ => ((((vlBdF B.fields.emb fun _ => Bm)⁻¹ τ : GL (Fin (B.R.N (i + 1))) B.LL) :
        Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.LL)ᵀ).map (Pl.iL w))
      g (Bs u μ w (i + 1) c') y (fun τ => -((I.rec7 l Z).chTw u μ).sDiv i τ)
      (fun τ => (lamT (B.hcW u) (i + 1) τ).detShift) hM eds hg3

end GlobalTheory.Mem.LocDictT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NearPair
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi

open scoped TensorProduct

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
  (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))

def NearV (P : SBof I a)
    (x : GL (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (B.R.m - 1))) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E ⊗[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))
    (g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) : Prop :=
  GlobalTheory.TwU.NearAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (GlobalTheory.Mem.Col2.ChartLevel.emb v x) (GlobalTheory.TwU.seamGL (sm I l Z) g)

def NearPair (P : SBof I a)
    (x : GL (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (B.R.m - 1))) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E ⊗[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))
    (g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z : B.fields.K) : Prop :=
  GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g z ∧ NearV I l Z a v P x g

def NearSet : Set (GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) :=
  {x | ∀ P : SBof I a, IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ g z, NearPair I l Z a v P x g z}


open Classical in
def valV (x : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) : ℂ :=
  (sm I l Z).σ₀ (∏ P : SBof I a,
    if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z then h.2.choose_spec.choose else 1)

end GlobalTheory.Mem.Col2.QChi

end
end

