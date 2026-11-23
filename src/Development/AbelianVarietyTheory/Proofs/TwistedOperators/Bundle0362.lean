module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0333
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
open scoped Classical

noncomputable section
namespace GlobalTheory.FinDecomp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in
def idem (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : AF F := pairA F 0 (singleFin v 1)

theorem af_ext' {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), evFin F u a = evFin F u b) : a = b :=
  Prod.ext h1 (af_ext fun u => h2 u)

theorem fst_idem (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : fstA F (idem F v) = 0 := rfl

theorem evFin_idem (v u : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : evFin F u (idem F v) = if u = v then 1 else 0 := by
  split_ifs with h
  · subst h; exact evalV_singleFin_self u 1
  · exact evalV_singleFin_ne h 1

theorem idem_mul_self (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : idem F v * idem F v = idem F v :=
  af_ext' (by simp [map_mul, fst_idem]) fun u => by rw [map_mul, evFin_idem]; split_ifs <;> simp

variable (F) in
def idemS (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) : AF F := ∑ v ∈ S, idem F v

theorem fst_idemS (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) : fstA F (idemS F S) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [idemS, map_sum, fst_idem]

theorem evFin_idemS (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (u : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : evFin F u (idemS F S) = if u ∈ S then 1 else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [idemS, map_sum, evFin_idem, Finset.sum_ite_eq]

theorem idemS_mul_self (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) : idemS F S * idemS F S = idemS F S :=
  af_ext' (by simp [map_mul, fst_idemS]) fun u => by rw [map_mul, evFin_idemS]; split_ifs <;> simp

theorem idem_mul_idemS_of_mem {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))} (h : w ∈ S) : idem F w * idemS F S = idem F w :=
  af_ext' (by simp [map_mul, fst_idemS, fst_idem]) fun u => by
    rw [map_mul, evFin_idemS, evFin_idem]; split_ifs with h1 h2 <;> simp_all

theorem idem_mul_idemS_of_notMem {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))} (h : w ∉ S) : idem F w * idemS F S = 0 :=
  af_ext' (by simp [map_mul, fst_idemS, fst_idem]) fun u => by
    rw [map_mul, evFin_idemS, evFin_idem, map_zero]; split_ifs with h1 h2 <;> simp_all

theorem mul_idem_of_evFin {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {a : AF F} (h : evFin F v a = 0) : a * idem F v = 0 :=
  af_ext' (by simp [map_mul, fst_idem]) fun u => by
    rw [map_mul, evFin_idem, map_zero]; split_ifs with hu
    · subst hu; simpa using h
    · simp

theorem idem_mul_of_at {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {a : AF F} (h : At (evFin F w) a) : idem F w * a = a := by
  have := h (1 - idem F w) (by simp [evFin_idem])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at this
  exact this.symm

end GlobalTheory.FinDecomp
end

noncomputable section
namespace GlobalTheory.FinDecomp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def phi (e : AF F) (M : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) := (1 - e) • 1 + e • M

theorem phi_mul {e : AF F} (he : e * e = e) (M N : Matrix (Fin n) (Fin n) (AE F E)) :
    phi e (M * N) = phi e M * phi e N := by
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  simp only [phi, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    h1, h2, h3, he, zero_smul, add_zero, zero_add]

theorem phi_mul_orth {e f : AF F} (hef : e * f = 0) (M : Matrix (Fin n) (Fin n) (AE F E)) :
    phi e M * phi f M = phi (e + f) M := by
  have hfe : f * e = 0 := by rw [mul_comm, hef]
  have h1 : (1 - f) * (1 - e) = 1 - (e + f) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hfe, sub_zero]; ring
  have h2 : (1 - f) * e = e := by rw [sub_mul, one_mul, hfe, sub_zero]
  have h3 : f * (1 - e) = f := by rw [mul_sub, mul_one, hfe, sub_zero]
  simp only [phi, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    h1, h2, h3, hfe, zero_smul, add_zero, add_smul]
  abel

theorem phi_one (M : Matrix (Fin n) (Fin n) (AE F E)) : phi (1 : AF F) M = M := by simp [phi]

theorem phi_zero (M : Matrix (Fin n) (Fin n) (AE F E)) : phi (0 : AF F) M = 1 := by simp [phi]

theorem phi_sub_one (e : AF F) (M : Matrix (Fin n) (Fin n) (AE F E)) : phi e M - 1 = e • (M - 1) := by
  simp only [phi, sub_smul, one_smul, smul_sub]; abel

theorem smul_phi_compl {a e : AF F} (h : a * e = 0) (M : Matrix (Fin n) (Fin n) (AE F E)) :
    a • phi (1 - e) M = a • M := by
  simp only [phi, smul_add, smul_smul, sub_sub_cancel, h, zero_smul, zero_add, mul_sub, mul_one, sub_zero]

theorem phi_unitary {σ : E →ₐ[F] E} {e : AF F} (he : e * e = e) {J M : Matrix (Fin n) (Fin n) (AE F E)}
    (hM : Mᵀ * J * M.map (cA σ) = J) : (phi e M)ᵀ * J * (phi e M).map (cA σ) = J := by
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have hm : (phi e M).map (cA σ) = (1 - e) • 1 + e • M.map (cA σ) := by
    ext i j
    simp only [phi, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add (f := _), map_smul, Matrix.one_apply]
    split_ifs <;> simp
  have ht : (phi e M)ᵀ = (1 - e) • 1 + e • Mᵀ := by simp [phi, Matrix.transpose_add, Matrix.transpose_smul]
  rw [hm, ht]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    h1, h2, h3, he, zero_smul, add_zero, zero_add, ← Matrix.mul_assoc, hM]
  rw [← add_smul, sub_add_cancel, one_smul]

section Loc

variable {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E}

theorem mat_mul (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : UA σ J) = 1 := rfl

theorem mat_mul_inv (g : UA σ J) : mat g * mat g⁻¹ = 1 := Units.mul_inv g.1

theorem mat_inv_mul (g : UA σ J) : mat g⁻¹ * mat g = 1 := Units.inv_mul g.1

theorem ua_ext {g h : UA σ J} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

def loc (e : AF F) (he : e * e = e) (g : UA σ J) : UA σ J :=
  ⟨⟨phi e (mat g), phi e (mat g⁻¹), by rw [← phi_mul he, mat_mul_inv]; simp only [phi]; rw [← add_smul, sub_add_cancel, one_smul],
      by rw [← phi_mul he, mat_inv_mul]; simp only [phi]; rw [← add_smul, sub_add_cancel, one_smul]⟩, phi_unitary he g.2⟩

theorem mat_loc (e : AF F) (he : e * e = e) (g : UA σ J) : mat (loc e he g) = phi e (mat g) := rfl

theorem mat_loc_inv (e : AF F) (he : e * e = e) (g : UA σ J) : mat (loc e he g)⁻¹ = phi e (mat g⁻¹) := rfl

end Loc

end GlobalTheory.FinDecomp
end

noncomputable section
namespace GlobalTheory.FinDecomp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E}

theorem idemS_insert {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))} (h : v ∉ S) :
    idemS F (insert v S) = idem F v + idemS F S := Finset.sum_insert h

theorem mat_prod_loc (g : UA σ J) : ∀ l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), l.Nodup →
    mat (l.map fun v => loc (idem F v) (idem_mul_self v) g).prod = phi (idemS F l.toFinset) (mat g)
  | [], _ => by simp [idemS, phi_zero, mat_one]
  | v :: t, hl => by
    rw [List.nodup_cons] at hl
    have hv : v ∉ t.toFinset := by simpa using hl.1
    rw [List.map_cons, List.prod_cons, mat_mul, mat_prod_loc g t hl.2, mat_loc, List.toFinset_cons,
      idemS_insert hv, phi_mul_orth (idem_mul_idemS_of_notMem hv)]

theorem exists_prod_local_mul_latStab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'), G.IsGood B →
    ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) = 0) →
    ∀ T₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∃ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)))
      (l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J),
    T₀ ⊆ S ∧ (∀ x ∈ l, x.1 ∈ S ∧ x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F x.1)) ∧
    h = (l.map Prod.snd).prod * k ∧
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) ∧
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) := by
  intro F E _ _ _ _ _ σ B a a' G hG h hinf T₀
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h) G.W.L hG.hW.lat
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h⁻¹) G.W.L hG.hW.lat
  set S := T₀ ∪ S₁ ∪ S₂ with hSdef
  have heS : idemS F S * idemS F S = idemS F S := idemS_mul_self S
  have heS' : (1 - idemS F S) * (1 - idemS F S) = 1 - idemS F S := by
    rw [sub_mul, one_mul, mul_sub, mul_one, heS, sub_self, sub_zero]
  have horth : idemS F S * (1 - idemS F S) = 0 := by rw [mul_sub, mul_one, heS, sub_self]
  set k := loc (1 - idemS F S) heS' h with hk
  have hl : ((S.toList.map fun v => (v, loc (idem F v) (idem_mul_self v) h)).map Prod.snd) =
      S.toList.map fun v => loc (idem F v) (idem_mul_self v) h := by
    rw [List.map_map]; rfl
  have hnot : ∀ w ∉ S, ∀ u : AF F, At (evFin F w) u → u * idemS F S = 0 := by
    intro w hw u hu
    rw [← idem_mul_of_at hu, mul_comm (idem F w), mul_assoc, idem_mul_idemS_of_notMem hw, mul_zero]
  have hgood : ∀ w ∉ S, ∀ (X : ℕ) (Xs : Spc F E X), ∀ γ, γ * (mat k)ᵀ ∈ latAtV Xs G.W w ↔ γ ∈ latAtV Xs G.W w := by
    intro w hw X Xs γ
    have hw1 : w ∉ S₁ := fun h' => hw (by simp [hSdef, h'])
    have hw2 : w ∉ S₂ := fun h' => hw (by simp [hSdef, h'])
    refine GlobalTheory.T.tensorLattice_mul_transpose_stable_iff F E X (a + a') Xs G.W w (mat k) (mat k⁻¹) (mat_inv_mul k) ?_ ?_ γ
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc, smul_phi_compl (hnot w hw u hu), Matrix.smul_mulVec]
      exact hS₁ w hw1 u hu hint y hy
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc_inv, smul_phi_compl (hnot w hw u hu), Matrix.smul_mulVec]
      exact hS₂ w hw2 u hu hint y hy
  refine ⟨S, S.toList.map fun v => (v, loc (idem F v) (idem_mul_self v) h), k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; simp [hSdef, hx]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    refine ⟨Finset.mem_toList.1 hv, ?_⟩
    intro u hu
    show u • (mat (loc (idem F v) (idem_mul_self v) h) - 1) = 0
    rw [mat_loc, phi_sub_one, smul_smul, mul_idem_of_evFin hu, zero_smul]
  · apply ua_ext
    rw [mat_mul, hl, mat_prod_loc h _ S.nodup_toList, Finset.toList_toFinset, hk, mat_loc, phi_mul_orth horth,
      add_sub_cancel, phi_one]
  · intro u hu
    rw [hk, mat_loc, phi_sub_one, smul_comm, hinf u hu, smul_zero]
  · intro w hw u hu
    have hu' := idem_mul_of_at hu
    have : u * (1 - idemS F S) = 0 := by
      calc u * (1 - idemS F S) = (idem F w * u) * (1 - idemS F S) := by rw [hu']
        _ = u * (idem F w - idem F w * idemS F S) := by ring
        _ = 0 := by rw [idem_mul_idemS_of_mem hw, sub_self, mul_zero]
    rw [hk, mat_loc, phi_sub_one, smul_smul, this, zero_smul]
  · exact fun w hw => hgood w hw a G.V
  · exact fun w hw => hgood w hw a' G.V'

end GlobalTheory.FinDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical TensorProduct

namespace GlobalTheory.WrongSignPair

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_tmul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (e : E) :
    piInf τ (a ⊗ₜ[F] e) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 e := rfl

private theorem star_extensionEmbedding_eq (h : IsCMExt F E σ) {w : InfinitePlace F} (x : w.Completion) :
    star (InfinitePlace.Completion.extensionEmbedding w x) = InfinitePlace.Completion.extensionEmbedding w x := by
  have h' := h
  obtain ⟨hF, -⟩ := h'
  have hw : w.IsReal := hF.isReal w
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  exact Complex.conj_ofReal _

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  have hconj := h
  obtain ⟨-, -, -, hconj⟩ := hconj
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have hz : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [cA]
    rw [hz, piInf_tmul, piInf_tmul, star_mul', star_extensionEmbedding_eq h, hconj]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, star_add]

private theorem trace_pi_real_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) :
    Algebra.trace ℝ (ι → ℝ) f = ∑ i, f i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun ℝ ι), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  simp

theorem trace_evI [IsTotallyReal F] (a : AF F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) =
      ∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re := by
  have hreal : ∀ v : InfinitePlace F, v.IsReal := IsTotallyReal.isReal
  haveI : IsEmpty {v : InfinitePlace F // v.IsComplex} :=
    ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.2 v.2) (hreal v.1)⟩
  rw [Algebra.trace_prod_apply]
  have h2 : (evI F a).2 = 0 := Subsingleton.elim _ _
  rw [h2, map_zero, add_zero, trace_pi_real_eq_sum]
  rw [← Fintype.sum_equiv (Equiv.subtypeUnivEquiv hreal) (fun v => (evI F a).1 v)
    (fun w => (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re) (fun v => ?_)]
  simp only [evI, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  show _ = (InfinitePlace.Completion.extensionEmbedding v.1 (a.1 v.1)).re
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply v.2, Complex.ofReal_re]

theorem trace_evI_trace (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : AE F E) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) z)) =
      ∑ w : InfinitePlace F, 2 * (piInf (τ w) z).re := by
  have hF : IsTotallyReal F := by
    have h' := h
    obtain ⟨hF, -⟩ := h'
    exact hF
  rw [trace_evI]
  refine Finset.sum_congr rfl fun w _ => ?_
  set t := Algebra.trace (AF F) (AE F E) z with ht
  have key : piInf (τ w) (algebraMap (AF F) (AE F E) t) = piInf (τ w) z + star (piInf (τ w) z) := by
    rw [ht, ← GlobalTheory.GaussMean.OneVec.add_sigR (AF F) h z, map_add (f := _), ← piInf_cA h]
    congr 2
  have hal : piInf (τ w) (algebraMap (AF F) (AE F E) t) =
      InfinitePlace.Completion.extensionEmbedding w (t.1 w) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, piInf_tmul, map_one,
      mul_one]
  rw [hal] at key
  rw [key, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

private theorem piInf_inclR_twisted_operators {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  have h1 : inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e := rfl
  have h2 : (1 : AF F).1 w = 1 := rfl
  rw [h1, piInf_tmul, h2, map_one, one_mul]

theorem piInf_hTens (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {n d : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (u u' : Matrix (Fin n) (Fin d) (AE F E)) :
    piInf τ (GlobalTheory.WeilM.hTens (cA σ) (incM F J) (incM F K) u u') =
      ∑ i, ∑ j, ∑ k, ∑ l, u.map (piInf τ) i j * J.map τ.1 i k * K.map τ.1 j l * star (u'.map (piInf τ) k l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.WeilM.hTens, incM, Matrix.map_apply, map_sum, map_mul, piInf_cA h, piInf_inclR_twisted_operators]

theorem sum_rank_one {n d : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (x x' : Fin n → ℂ)
    (y y' : Fin d → ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, vecMulVec x y i j * G i k * H j l * star (((-Complex.I) • vecMulVec x' y') k l) =
      (x ⬝ᵥ G *ᵥ star x') * (y ⬝ᵥ (Complex.I • H) *ᵥ star y') := by
  have hI : star (-Complex.I) = Complex.I := by
    rw [star_neg]
    exact (congrArg Neg.neg Complex.conj_I).trans (neg_neg _)
  simp only [dotProduct, mulVec, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul, star_mul', hI,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem star_dotProduct_mulVec_star_comm {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i j, star (G j i) = G i j)
    (u v : Fin n → ℂ) : star (u ⬝ᵥ G *ᵥ star v) = v ⬝ᵥ G *ᵥ star u := by
  simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  first
  | (rw [Finset.sum_comm]
     refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
     rw [hG]; ring)
  | (refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
     rw [hG]; ring)

private theorem dotProduct_mulVec_star_invariant {n : ℕ} {G θ : Matrix (Fin n) (Fin n) ℂ} (hθ : θᵀ * G * θ.map star = G)
    (u v : Fin n → ℂ) : (θ *ᵥ u) ⬝ᵥ G *ᵥ star (θ *ᵥ v) = u ⬝ᵥ G *ᵥ star v := by
  have hs : star (θ *ᵥ v) = θ.map star *ᵥ star v := by
    ext i
    simp [mulVec, dotProduct, star_sum, star_mul']
  rw [hs, ← Matrix.vecMul_transpose θ u, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [hθ]

theorem majorant_im {n : ℕ} {G θ : Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i j, star (G j i) = G i j) (h : IsCartan G θ)
    (x : Fin n → ℂ) : ((θ *ᵥ x) ⬝ᵥ G *ᵥ star x).im = 0 := by
  obtain ⟨h1, h2, -⟩ := h
  have e1 : (θ *ᵥ x) ⬝ᵥ G *ᵥ star x = x ⬝ᵥ G *ᵥ star (θ *ᵥ x) := by
    conv_lhs => rw [← dotProduct_mulVec_star_invariant h2 (θ *ᵥ x) x, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [← star_dotProduct_mulVec_star_comm hG (θ *ᵥ x) x] at e1
  exact Complex.conj_eq_iff_im.mp e1.symm

private theorem mul_vecMulVec_mul_transpose' {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin d) (Fin d) ℂ)
    (x : Fin n → ℂ) (y : Fin d → ℂ) : A * vecMulVec x y * Cᵀ = vecMulVec (A *ᵥ x) (C *ᵥ y) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  first
  | (rw [Finset.sum_comm]
     exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
  | exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private theorem re_pos_im_zero_of_isCartan {n : ℕ} {G θ : Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i j, star (G j i) = G i j)
    (h : IsCartan G θ) {x : Fin n → ℂ} (hx : x ≠ 0) :
    0 < (x ⬝ᵥ G *ᵥ star (θ *ᵥ x)).re ∧ (x ⬝ᵥ G *ᵥ star (θ *ᵥ x)).im = 0 := by
  have hi := majorant_im hG h x
  have hp := h.2.2 x hx
  rw [← star_dotProduct_mulVec_star_comm hG (θ *ᵥ x) x, Complex.star_def, Complex.conj_re, Complex.conj_im, hi, neg_zero]
  exact ⟨hp, rfl⟩

theorem exists_neg_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → 0 < n → 0 < d →
    ∀ (ε' : InfinitePlace F → ℤˣ) (w : InfinitePlace F), ε' w = -1 →
    ∃ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u ∧ At (evI F) u' ∧
      (∀ w', u'.map (piInf (B.emb w')) =
        (((ε' w' : ℤ) : ℂ) * Complex.I) • (X.θ w' * u.map (piInf (B.emb w')) * (W.θ w')ᵀ)) ∧
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (GlobalTheory.WeilM.symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u')) < 0 := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW hn hd ε' w hw
  have h : IsCMExt F E σ := hB.cm
  have hconj : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x) := by
    have h' := h
    obtain ⟨-, -, -, hconj⟩ := h'
    exact hconj
  have lift : ∀ c : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ, ∃ z : Matrix (Fin n) (Fin d) (AE F E),
      At (evI F) z ∧ ∀ w', z.map (piInf (B.emb w')) = c w' := by
    intro c
    have hz := fun i j => GlobalTheory.ThK.exists_at_evI_piInf_eq F E σ h B.emb (fun w' => c w' i j)
    choose z hz1 hz2 using hz
    refine ⟨z, ?_, ?_⟩
    · intro a ha
      ext i j
      exact hz1 i j a ha
    · intro w'
      ext i j
      exact hz2 i j w'
  let x : Fin n → ℂ := Pi.single ⟨0, hn⟩ 1
  let y : Fin d → ℂ := Pi.single ⟨0, hd⟩ 1
  have hx : x ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hn⟩
    simp [x] at this
  have hy : y ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hd⟩
    simp [y] at this
  obtain ⟨u, hu1, hu2⟩ := lift (fun w' => if w' = w then vecMulVec x y else 0)
  obtain ⟨u', hu'1, hu'2⟩ := lift (fun w' => (((ε' w' : ℤ) : ℂ) * Complex.I) •
    (X.θ w' * (if w' = w then vecMulVec x y else 0) * (W.θ w')ᵀ))
  have hu : ∀ w', u.map (piInf (B.emb w')) = if w' = w then vecMulVec x y else 0 := fun w' => hu2 w'
  have hu' : ∀ w', u'.map (piInf (B.emb w')) = (((ε' w' : ℤ) : ℂ) * Complex.I) •
      (X.θ w' * (if w' = w then vecMulVec x y else 0) * (W.θ w')ᵀ) := fun w' => hu'2 w'
  refine ⟨u, u', hu1, hu'1, fun w' => by rw [hu' w', hu w'], ?_⟩
  have hJ : ∀ i j, star ((X.J.map (B.emb w).1) j i) = (X.J.map (B.emb w).1) i j := by
    intro i j
    simp only [Matrix.map_apply]
    rw [← hconj, hX.herm]
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hK : ∀ i j, star ((Complex.I • W.J.map (B.emb w).1) j i) = (Complex.I • W.J.map (B.emb w).1) i j := by
    intro i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [star_mul', hI, ← hconj, hW.skew, map_neg]
    ring
  obtain ⟨hPr, hPi⟩ := re_pos_im_zero_of_isCartan hJ (hX.cartan w) hx
  obtain ⟨hQr, hQi⟩ := re_pos_im_zero_of_isCartan hK (hW.cartan w) hy
  have hs : (((ε' w : ℤ) : ℂ) * Complex.I) = -Complex.I := by
    rw [hw]
    simp
  have hmain : piInf (B.emb w) (GlobalTheory.WeilM.hTens (cA σ) (incM F X.J) (incM F W.J) u u') =
      (x ⬝ᵥ (X.J.map (B.emb w).1) *ᵥ star (X.θ w *ᵥ x)) *
        (y ⬝ᵥ (Complex.I • W.J.map (B.emb w).1) *ᵥ star (W.θ w *ᵥ y)) := by
    rw [piInf_hTens h, hu w, hu' w, if_pos rfl, hs, mul_vecMulVec_mul_transpose', sum_rank_one]
  have hzero : ∀ w', w' ≠ w → piInf (B.emb w') (GlobalTheory.WeilM.hTens (cA σ) (incM F X.J) (incM F W.J) u u') = 0 := by
    intro w' hne
    rw [piInf_hTens h, hu w', if_neg hne]
    simp
  simp only [GlobalTheory.WeilM.symp]
  rw [trace_evI_trace h B.emb, Finset.sum_eq_single w]
  · rw [map_mul, map_neg, map_one, neg_one_mul, hmain, Complex.neg_re, Complex.mul_re, hPi, zero_mul, sub_zero]
    nlinarith [mul_pos hPr hQr]
  · intro w' _ hne
    rw [map_mul, hzero w' hne, mul_zero, Complex.zero_re, mul_zero]
  · intro hw'
    exact absurd (Finset.mem_univ w) hw'

end GlobalTheory.WrongSignPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitriangularStabilizerOfPrincipalMoveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitriangularStabilizer_of_principal_move : ∀ {D : D7} (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) (Q : GlobalTheory.FinPl.Pl D → Prop) (g k : GA D W) (u : UX D ρ), g ∈ grpAt W Q → k ∈ grpAt W Q → MxOff Q (mt W k ⬝ x - mt W g⁻¹ ⬝ (x ⬝ u.1.1)) → ∃ r ∈ Rgrp W x, r ∈ grpAt W Q ∧ g = r * k⁻¹ := by
  first | exact @GlobalTheory.PrincipalMove.exists_move | exact GlobalTheory.PrincipalMove.exists_move | (intros; apply GlobalTheory.PrincipalMove.exists_move <;> assumption)
end

