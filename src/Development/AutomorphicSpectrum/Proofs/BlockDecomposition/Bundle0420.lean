module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemParabolicIffMemEmbedded
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.IotaMem

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iotaM_castSucc_castSucc (n : ℕ) (y : Mir k n) (r c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.castSucc r) (Fin.castSucc c) =
      ((y : GL (Fin (n + 1)) k) : Matrix _ _ k) r c := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

theorem iotaM_last_castSucc (n : ℕ) (y : Mir k n) (c : Fin (n + 1)) :
    (((embedding₂ k n y : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix _ _ k) (Fin.last (n + 1)) (Fin.castSucc c) = 0 := by
  simp only [embedding₂, MonoidHom.coe_comp, Function.comp_apply]
  unfold levi
  simp [glEmb, glEmbHom, glEmbMat]

end GlobalTheory.CompanionTheory.LeibPhi.IotaMem

namespace GlobalTheory.CompanionTheory.LeibPhi


open GlobalTheory.CompanionTheory.LeibPhi.IotaMem in
theorem mem_mirabolicParabolic_iff_iotaM_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (y : Mir k (m + j)) :
    y ∈ MirabolicParabolic k m j ↔ embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1) := by
  have mem_iff (m j : ℕ) (g : Mir k (m + j)) :
      g ∈ MirabolicParabolic k m j ↔ ∀ (b : Fin (j + 1)) (a : Fin m),
        ((g : GL (Fin (m + j + 1)) k) : Matrix _ _ k)
          (eGP m j ⟨true, b⟩) (eGP m j ⟨false, a⟩) = 0 := by
    show (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j) ↔ _
    rw [mem_parab_iff]
    constructor
    · intro h b a
      exact h true false b a (by decide)
    · intro h x y i l hxy
      cases x <;> cases y <;> first | exact absurd hxy (by decide) | exact h i l
  rw [mem_iff, mem_iff]
  have eF : ∀ a : Fin m, eGP m (j + 1) ⟨false, a⟩ = Fin.castSucc (eGP m j ⟨false, a⟩) := by
    intro a
    ext
    simp [blockIndex_false_val]
  have eT : ∀ b : Fin (j + 1),
      eGP m (j + 1) ⟨true, Fin.castSucc b⟩ = Fin.castSucc (eGP m j ⟨true, b⟩) := by
    intro b
    ext
    simp [blockIndex_true_val]
  have eL : eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩ = Fin.last (m + j + 1) := by
    ext
    simp [blockIndex_true_val]
    omega
  constructor
  · intro h b a
    induction b using Fin.lastCases with
    | last =>
      rw [eL, eF]
      exact iotaM_last_castSucc k (m + j) y _
    | cast b =>
      rw [eT, eF]
      rw [iotaM_castSucc_castSucc k (m + j) y]
      exact h b a
  · intro h b a
    have hb := h (Fin.castSucc b) a
    rw [eT, eF, iotaM_castSucc_castSucc k (m + j) y] at hb
    exact hb

end GlobalTheory.CompanionTheory.LeibPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRatCentTwConj
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj twConj_mul_left mem_twCent)

namespace GlobalTheory.CompanionTheory.OrbInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thetaA_ratGL (g : GL (Fin n) E) : thetaA E n (ratGL E n g) = ratGL E n (thetaE E n g) := by
  have h : ∀ g : GL (Fin n) E, (ratGL E n g).val = g.val.map (algebraMap E (Ad E)) := fun _ => rfl
  apply Units.ext
  rw [thetaR_val, ← map_inv, h, h, thetaR_val]
  ext i j
  exact conjAd_algebraMap _

theorem twConj_ratGL (g d : GL (Fin n) E) (x : GA E n) :
    twConj (thetaA E n) x (ratGL E n (twConj (thetaE E n) g d)) =
      twConj (thetaA E n) (ratGL E n g * x) (ratGL E n d) := by
  simp only [twConj, map_mul, map_inv, thetaA_ratGL]
  group

theorem mem_ratCent_twConj (g d : GL (Fin n) E) (x : GA E n) :
    x ∈ ratCent (twConj (thetaE E n) g d) ↔ ratGL E n g * x * (ratGL E n g)⁻¹ ∈ ratCent d := by
  simp only [ratCent, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' := (mem_twCent _ _ _).1 hc
    simp only [twConj] at hc'
    refine ⟨g * c * g⁻¹, (mem_twCent _ _ _).2 ?_, by simp only [map_mul, map_inv]⟩
    simp only [map_mul, map_inv]
    calc (g * c * g⁻¹)⁻¹ * d * (thetaE E n g * thetaE E n c * (thetaE E n g)⁻¹)
        = g * (c⁻¹ * (g⁻¹ * d * thetaE E n g) * thetaE E n c) * (thetaE E n g)⁻¹ := by group
      _ = g * (g⁻¹ * d * thetaE E n g) * (thetaE E n g)⁻¹ := by rw [hc']
      _ = d := by group
  · rintro ⟨c, hc, h⟩
    have hc' := (mem_twCent _ _ _).1 hc
    refine ⟨g⁻¹ * c * g, (mem_twCent _ _ _).2 ?_, ?_⟩
    · simp only [twConj, map_mul, map_inv]
      calc (g⁻¹ * c * g)⁻¹ * (g⁻¹ * d * thetaE E n g) *
            ((thetaE E n g)⁻¹ * thetaE E n c * thetaE E n g)
          = g⁻¹ * (c⁻¹ * d * thetaE E n c) * thetaE E n g := by group
        _ = g⁻¹ * d * thetaE E n g := by rw [hc']
    · simp only [map_mul, map_inv, h]
      group

theorem twConj_ratCent (d : GL (Fin n) E) {h : GA E n} (hh : h ∈ ratCent d) (x : GA E n) :
    twConj (thetaA E n) (h * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) := by
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hh
  have hc' := (mem_twCent _ _ _).1 hc
  refine twConj_mul_left _ _ ((mem_twCent _ _ _).2 ?_) x
  rw [thetaA_ratGL, ← map_inv, ← map_mul, ← map_mul, hc']

theorem countable_ratCent [Countable (GL (Fin n) E)] (d : GL (Fin n) E) :
    (ratCent d : Set (GA E n)).Countable :=
  (Set.countable_range (ratGL E n)).mono (by
    rintro _ ⟨c, -, rfl⟩
    exact ⟨c, rfl⟩)

theorem orbInvOf : OrbInvOf := by
  intro hQ hT E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ φ d₁ g₁ d₂ g₂ hc
  obtain ⟨⟨lc₁, sc₁, t₁⟩, -, -, cn₁, -, -⟩ := hT E a
  obtain ⟨⟨lc₂, sc₂, t₂⟩, -, -, cn₂, -, -⟩ := hT E b
  have hcnt : (((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) :
      Set (GA E a × GA E b)).Countable := by
    rw [Subgroup.coe_prod]
    exact (countable_ratCent d₁).prod (countable_ratCent d₂)
  have : Countable ((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) := hcnt.to_subtype
  set F : GA E a × GA E b → ℂ := fun x =>
    φ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂)) with hF
  have key := hQ (GA E a × GA E b) (μ₁.prod μ₂) ((ratCent d₁).prod (ratCent d₂))
    ((ratCent (twConj (thetaE E a) g₁ d₁)).prod (ratCent (twConj (thetaE E b) g₂ d₂))) F
    (ratGL E a g₁, ratGL E b g₂) hc.measurable
    (fun h hh x => by
      simp only [hF, Prod.fst_mul, Prod.snd_mul]
      rw [twConj_ratCent d₁ hh.1, twConj_ratCent d₂ hh.2])
    (fun x => by
      simp only [Subgroup.mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
        mem_ratCent_twConj])
  simp only [hF, Prod.fst_mul, Prod.snd_mul] at key
  simp only [orbTerm2, twConj_ratGL]
  exact key

end GlobalTheory.CompanionTheory.OrbInv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureData
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Grp

section Alg

variable {k : Type} [Field k]

theorem mirProj_eq_one_of_mem {n : ℕ} (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  obtain ⟨v, hv⟩ := (Subgroup.mem_subgroupOf.1 hu : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  apply Units.ext
  ext a b
  show ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _
  rw [← hv]
  simp [unip, colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one' {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) : u ∈ MirUin k n := by
  have hb : ∀ a b : Fin n, ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = if a = b then 1 else 0 := by
    intro a b
    have := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) a b) hu
    exact (this : ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _).trans (by simp [Matrix.one_apply])
  have hl := (mem_Mir_iff k (u : GL (Fin (n + 1)) k)).1 u.2
  refine Subgroup.mem_subgroupOf.2 ⟨Multiplicative.ofAdd fun a => ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.last n), ?_⟩
  apply Units.ext
  ext a b
  have hlb := congrFun hl b
  induction a using Fin.lastCases with
  | last =>
    rw [hlb]
    induction b using Fin.lastCases <;> simp [unip, colMat, Matrix.one_apply, eLast, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  | cast a =>
    induction b using Fin.lastCases with
    | last => simp [unip, colMat, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast b =>
      rw [hb]
      simp [unip, colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mirUin_normal (n : ℕ) : (MirUin k n).Normal := by
  refine ⟨fun u hu g => mem_of_mirProj_eq_one' _ ?_⟩
  rw [map_mul, map_mul, mirProj_eq_one_of_mem u hu, mul_one, map_inv, mul_inv_cancel]

theorem mirUin_comm {n : ℕ} {a b : Mir k n} (ha : a ∈ MirUin k n) (hb : b ∈ MirUin k n) : a * b = b * a := by
  obtain ⟨v, hv⟩ := (Subgroup.mem_subgroupOf.1 ha : ((a : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 hb : ((b : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  apply Subtype.ext
  show (a : GL (Fin (n + 1)) k) * (b : GL (Fin (n + 1)) k) = (b : GL (Fin (n + 1)) k) * (a : GL (Fin (n + 1)) k)
  rw [← hv, ← hw, ← map_mul, mul_comm, map_mul]

def prodSub {n : ℕ} (L₁ L₂ : Subgroup (Mir k n)) (h₁ : L₁ ≤ MirUin k n) (h₂ : L₂ ≤ MirUin k n) : Subgroup (Mir k n) where
  carrier := (L₁ : Set (Mir k n)) * (L₂ : Set (Mir k n))
  one_mem' := ⟨1, L₁.one_mem, 1, L₂.one_mem, one_mul 1⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    refine ⟨a * c, L₁.mul_mem ha hc, b * d, L₂.mul_mem hb hd, ?_⟩
    show a * c * (b * d) = a * b * (c * d)
    rw [mul_assoc a c, ← mul_assoc c b, mirUin_comm (h₁ hc) (h₂ hb)]
    simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, L₁.inv_mem ha, b⁻¹, L₂.inv_mem hb, ?_⟩
    show a⁻¹ * b⁻¹ = (a * b)⁻¹
    rw [_root_.mul_inv_rev]
    exact mirUin_comm (MirUin k n |>.inv_mem (h₁ ha)) (MirUin k n |>.inv_mem (h₂ hb))

theorem hpg_entry {i t : ℕ} (g : Mir k ((i + 1) + t + 1)) (hg : g ∈ HPG k (i + 1) (t + 1))
    (l : Fin ((i + 1) + t + 2)) (hl : i < l.val) (hl2 : l.val ≠ (i + 1) + t + 1) (c : Fin (i + 1)) :
    ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) l
      (Fin.castLE (by omega) c) = 0 := by
  have hp : (g : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ GlobalTheory.SmGL.parab k (ePG (i + 1) (t + 1)) := hg
  have hlt := l.isLt
  have h0 := mem_parab_iff.1 hp true false (⟨l.val - (i + 1), by omega⟩ : Fin (t + 1)) (Fin.castSucc c : Fin (i + 1 + 1)) (by decide)
  have e1 : ePG (i + 1) (t + 1) ⟨true, (⟨l.val - (i + 1), by omega⟩ : Fin (t + 1))⟩ = l := by
    apply Fin.ext
    simp [ePG, two]
    omega
  have e2 : ePG (i + 1) (t + 1) ⟨false, (Fin.castSucc c : Fin (i + 1 + 1))⟩ = Fin.castLE (by omega) c := by
    apply Fin.ext
    simp [ePG, two]
  rw [e1, e2] at h0
  exact h0

theorem Cl_left {i t : ℕ} (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1)) (x : Mir k ((i + 1) + t + 1))
    (hx : x ∈ Cl k i t) : h * x ∈ Cl k i t := by
  intro c
  rw [_root_.mul_inv_rev]
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h1 : l.val ≤ i
  · have := hx ⟨l.val, by omega⟩
    have e : Fin.castLE (by omega) (⟨l.val, by omega⟩ : Fin (i + 1)) = l := Fin.ext rfl
    rw [e] at this
    rw [this, zero_mul]
  · by_cases h2 : l.val = (i + 1) + t + 1
    · have e : l = Fin.last _ := Fin.ext h2
      have hm := (mem_Mir_iff k ((h⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k)).1 (h⁻¹).2
      have hc := congrFun hm (Fin.castLE (by omega) c)
      rw [e, hc]
      have : Fin.castLE (by omega) c ≠ Fin.last ((i + 1) + t + 1) := by
        intro e'
        have := congrArg Fin.val e'
        simp at this
        omega
      simp [eLast, Pi.single_apply, this]
    · rw [hpg_entry _ ((HPG k (i + 1) (t + 1)).inv_mem hh) l (by omega) h2 c, mul_zero]

theorem Cl_right {i t : ℕ} (x : Mir k ((i + 1) + t + 1)) (hx : x ∈ Cl k i t) (u : Mir k ((i + 1) + t + 1))
    (hu : u ∈ MirUin k ((i + 1) + t + 1)) : x * u ∈ Cl k i t := by
  intro c
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 ((MirUin k ((i + 1) + t + 1)).inv_mem hu) :
    ((u⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) ∈ MirU k ((i + 1) + t + 1))
  rw [_root_.mul_inv_rev]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [← hw]
  have hv : ((unip k ((i + 1) + t + 1) w : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) = 1 + colMat k _ w.toAdd := rfl
  rw [hv, add_mul, one_mul, Matrix.add_apply, hx c, zero_add, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = Fin.last _
  · have hm := (mem_Mir_iff k ((x⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k)).1 (x⁻¹).2
    have hc := congrFun hm (Fin.castLE (by omega) c)
    rw [hl, hc]
    have : Fin.castLE (by omega) c ≠ Fin.last ((i + 1) + t + 1) := by
      intro e'
      have := congrArg Fin.val e'
      simp at this
      omega
    simp [eLast, Pi.single_apply, this]
  · simp [colMat, hl]

end Alg

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mirChar_ker_open (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) :
    IsOpen ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) := by
  have he : ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) =
      (fun u : MirUin k (n + 1) => GlobalTheory.CompanionTheory.BZFun.lastCol k u (Fin.last n)) ⁻¹' {x : k | ψ x = 1} := by
    ext u
    obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k (n + 1)) : GL (Fin (n + 2)) k) ∈ MirU k (n + 1))
    have hl : GlobalTheory.CompanionTheory.BZFun.lastCol k u (Fin.last n) = w.toAdd (Fin.last n) := by
      simp only [GlobalTheory.CompanionTheory.BZFun.lastCol, ← hw]
      exact unip_apply_castSucc_last k (n + 1) w _
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq, hl,
      mirChar_eq k ψ n u w hw.symm]
    constructor
    · intro h
      apply Circle.ext
      simpa using congrArg Units.val h
    · intro h
      rw [h, map_one]
  rw [he]
  exact (GlobalTheory.CompanionTheory.BZFun.isOpen_addChar_eq_one k ψ hψ).preimage
    ((continuous_apply _).comp (GlobalTheory.CompanionTheory.BZFun.continuous_lastCol k (n + 1)))

theorem isClosed_Cl (i t : ℕ) : IsClosed (Cl k i t) := by
  have hc : Continuous fun p : Mir k ((i + 1) + t + 1) =>
      (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
  have he : Cl k i t = ⋂ c : Fin (i + 1), {p : Mir k ((i + 1) + t + 1) |
      (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
        (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castLE (by omega) c) = 0} := by
    ext p
    simp [Cl]
  rw [he]
  exact isClosed_iInter fun c => isClosed_eq (hc.matrix_elem _ _) continuous_const

end Top

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) (i t : ℕ),
  (MirUin k ((i + 1) + t + 1)).Normal ∧ IsOpen ((mirChar k ψ ((i + 1) + t)).ker : Set (MirUin k ((i + 1) + t + 1))) ∧
    IsClosed (Cl k i t) ∧ (∀ h ∈ HPG k (i + 1) (t + 1), ∀ x ∈ Cl k i t, h * x ∈ Cl k i t) ∧
    (∀ x ∈ Cl k i t, ∀ u ∈ MirUin k ((i + 1) + t + 1), x * u ∈ Cl k i t) ∧
    ∀ L₁ L₂ : Subgroup (Mir k ((i + 1) + t + 1)), L₁ ≤ MirUin k ((i + 1) + t + 1) → L₂ ≤ MirUin k ((i + 1) + t + 1) →
      IsCompact (L₁ : Set (Mir k ((i + 1) + t + 1))) → IsCompact (L₂ : Set (Mir k ((i + 1) + t + 1))) →
      ∃ L : Subgroup (Mir k ((i + 1) + t + 1)), L ≤ MirUin k ((i + 1) + t + 1) ∧ IsCompact (L : Set (Mir k ((i + 1) + t + 1))) ∧
        L₁ ≤ L ∧ L₂ ≤ L := by
  intro k _ _ _ _ ψ hψ i t
  refine ⟨mirUin_normal _, mirChar_ker_open ψ hψ _, isClosed_Cl i t, fun h hh x hx => Cl_left h hh x hx,
    fun x hx u hu => Cl_right x hx u hu, fun L₁ L₂ h₁ h₂ c₁ c₂ => ⟨prodSub L₁ L₂ h₁ h₂, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact (MirUin k _).mul_mem (h₁ ha) (h₂ hb)
  · exact (c₁.mul c₂ : IsCompact ((L₁ : Set (Mir k ((i + 1) + t + 1))) * (L₂ : Set (Mir k ((i + 1) + t + 1)))))
  · intro a ha
    exact ⟨a, ha, 1, L₂.one_mem, mul_one a⟩
  · intro b hb
    exact ⟨1, L₁.one_mem, b, hb, one_mul b⟩

end GlobalTheory.CompanionTheory.BZPhiPG.Grp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentNormal
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.UNorm

theorem mirProj_eq_one_of_mem {k : Type} [Field k] {n : ℕ} (u : Mir k n) (hu : u ∈ MirUin k n) :
    mirabolicProjection k n u = 1 := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  apply Units.ext
  ext i j
  change ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc j.castSucc =
    (1 : Matrix (Fin n) (Fin n) k) i j
  rw [← hv]
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) i.castSucc j.castSucc = _
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one {k : Type} [Field k] {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) :
    u ∈ MirUin k n := by
  have hrow := (GlobalTheory.BZMir.mem_Mir_iff k (u : GL (Fin (n + 1)) k)).mp u.2
  have hrow' : ∀ j, ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
      (Pi.single (Fin.last n) (1 : k) : Fin (n + 1) → k) j := by
    intro j
    rw [hrow]
    rfl
  have hblk : ∀ i j : Fin n,
      ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc j.castSucc =
        (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    exact congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hu
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd (fun i : Fin n =>
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc (Fin.last n)), ?_⟩
  apply Units.ext
  ext i j
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd (Multiplicative.ofAdd (fun i : Fin n =>
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc (Fin.last n))))) i j = _
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [GlobalTheory.BZMir.colMat, hrow']
    | cast j =>
      simp [GlobalTheory.BZMir.colMat, hrow', Matrix.one_apply, Pi.single_apply, Fin.castSucc_ne_last,
        (Fin.castSucc_ne_last j).symm]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast j => simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last, hblk]

theorem mirUin_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ), (MirUin k n).Normal := by
  intro k _ _ _ _ n
  refine ⟨fun u hu g => ?_⟩
  apply GlobalTheory.CompanionTheory.LeibPhi.UNorm.mem_of_mirProj_eq_one
  rw [map_mul, map_mul, map_inv, GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirProj_eq_one_of_mem u hu,
    mul_one, mul_inv_cancel]

end GlobalTheory.CompanionTheory.LeibPhi.UNorm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusMirabolicBlockFactor
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

theorem dpowM_hgp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (s : ℝ) (h : MirabolicParabolic k (i + 1) t), dpowM ((i + 1) + t) s (h : Mir k ((i + 1) + t)) = dpow (i + 1) s (gpProj k (i + 1) t h).1 * dpow (t + 1) s (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) := by
  intro k _ _ _ _ i t s h
  have key : ∀ (n : ℕ) (g : GL (Fin n) k),
      GlobalTheory.BZMir.Leib.dpow n s g = GlobalTheory.SmGL.absPow k (s : ℂ) (Matrix.GeneralLinearGroup.det g) :=
    fun _ _ => rfl
  have hdet : Matrix.GeneralLinearGroup.det
      ((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) =
      Matrix.GeneralLinearGroup.det (GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).1 *
        Matrix.GeneralLinearGroup.det
          (((GlobalTheory.BZMir.Leib.gpProj k (i + 1) t h).2 : GlobalTheory.BZMir.Mir k t) :
            GL (Fin (t + 1)) k) := by
    have hp := GlobalTheory.SmGL.det_parab k (GlobalTheory.BZMir.Leib.eGP (i + 1) t)
      (GlobalTheory.BZMir.Leib.hgpIncl k (i + 1) t h)
    rw [Fintype.prod_bool] at hp
    exact hp.trans (mul_comm _ _)
  rw [show GlobalTheory.RgGu.Leib.dpowM ((i + 1) + t) s (h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) =
      GlobalTheory.BZMir.Leib.dpow ((i + 1) + t + 1) s
        ((h : GlobalTheory.BZMir.Mir k ((i + 1) + t)) : GL (Fin ((i + 1) + t + 1)) k) from rfl,
    key, key, key, hdet, map_mul]

end GlobalTheory.CompanionTheory.BZPhiPG

end
end

