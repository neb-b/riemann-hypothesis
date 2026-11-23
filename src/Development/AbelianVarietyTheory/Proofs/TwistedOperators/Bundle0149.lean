module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
section
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.IwahoriInj ValuativeRel

namespace GlobalTheory.JacInj

section Abstract

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π₁ : Representation ℂ G V} {π : Representation ℂ G W}

theorem map_apply' (f : π₁.IntertwiningMap π) (g : G) (v : V) : f (π₁ g v) = π g (f v) := by
  have h := LinearMap.congr_fun (f.isIntertwining' g) v
  simpa using h

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem mem_twKer_of_map (f : π₁.IntertwiningMap π) (hπ : IsSmooth π) (hf : Function.Injective f)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) {v : V} (hv : f v ∈ twKer π H 1) :
    v ∈ twKer π₁ H 1 := by
  have h₁ : IsSmooth π₁ := by
    intro w
    have hset : {g : G | π₁ g w = w} = {g : G | π g (f w) = f w} := by
      ext g
      simp only [Set.mem_ofPred_eq, ← map_apply' f g w]
      exact hf.eq_iff.symm
    rw [hset]
    exact hπ (f w)
  obtain ⟨U, -, hU, hUv⟩ := GlobalTheory.LocGL.exists_normal_fix h₁ hH v
  letI : Fintype (H ⧸ U) := U.fintypeQuotientOfFiniteIndex
  have hUf : ∀ u ∈ U, π (u : H) (f v) = f v := fun u hu => by rw [← map_apply', hUv u hu]
  rw [← GlobalTheory.LocGL.idem_eq_zero_iff h₁ hH]
  apply hf
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, GlobalTheory.LocGL.idem_eq_cosetSum h₁ hH U hUv, map_smul, map_sum]
  simp only [map_apply']
  rw [← GlobalTheory.LocGL.idem_eq_cosetSum hπ hH U hUf]
  exact (GlobalTheory.LocGL.idem_eq_zero_iff hπ hH).2 hv

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

def wt (e : (Σ a, m a) ≃ n) (M : ℕ) (i j : n) : ℤ :=
  M * (((Finset.univ.filter (· < blk e i)).card : ℤ) - (Finset.univ.filter (· < blk e j)).card)

theorem conc_wt (e : (Σ a, m a) ≃ n) (M : ℕ) : Conc (wt e M) := by
  unfold GlobalTheory.IwahoriInj.Conc
  refine ⟨fun i => by simp [wt], fun i j l => le_of_eq ?_⟩
  simp only [wt]
  ring

private theorem eventually_valuation_le_uniformizer_pow_of_mem_unipRad (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ unipRad k e) (i j : n) :
    ∀ᶠ M : ℕ in Filter.atTop, valuation k ((g : Matrix n n k) i j) ≤ uniformizer k ^ wt e M i j := by
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hg
  rw [mem_parab] at hP
  have hmono : ∀ a b : ℤ, a ≤ b → uniformizer k ^ b ≤ uniformizer k ^ a := by
    intro a b hab
    exact zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le hab
  rcases lt_trichotomy (blk e i) (blk e j) with h | h | h
  ·
    obtain ⟨N, hN⟩ := MulArchimedean.arch (valuation k ((g : Matrix n n k) i j))
      ((one_lt_inv₀ uniformizer_pos).2 uniformizer_lt_one)
    have hss : Finset.univ.filter (· < blk e i) ⊂ Finset.univ.filter (· < blk e j) := by
      refine (Finset.ssubset_iff_of_subset (fun x hx => ?_)).2 ⟨blk e i, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.trans h
      · simp [h]
      · simp
    have hlt := Finset.card_lt_card hss
    filter_upwards [Filter.eventually_ge_atTop N] with M hM
    have hM' : (N : ℤ) ≤ M := by exact_mod_cast hM
    have hd : ((Finset.univ.filter (· < blk e i)).card : ℤ) -
        (Finset.univ.filter (· < blk e j)).card ≤ -1 := by omega
    have hw : wt e M i j ≤ -(N : ℤ) := by
      simp only [wt]
      nlinarith
    refine hN.trans (le_trans (le_of_eq ?_) (hmono _ _ hw))
    rw [zpow_neg, zpow_natCast, inv_pow]
  ·
    refine Filter.Eventually.of_forall fun M => ?_
    have hw : wt e M i j = 0 := by simp [wt, h]
    rw [hw, zpow_zero]
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at h
    cases h
    rw [hD _ i' j', Matrix.one_apply]
    split_ifs <;> simp
  ·
    exact Filter.Eventually.of_forall fun M => by
      rw [hP i j h, map_zero]
      exact zero_le'

theorem eventually_mem_grp (e : (Σ a, m a) ≃ n) {u : GL n k} (hu : u ∈ unipRad k e) :
    ∀ᶠ M : ℕ in Filter.atTop, u ∈ grp k (conc_wt e M) := by
  unfold GlobalTheory.IwahoriInj.grp
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  unfold GlobalTheory.IwahoriInj.Deep
  have hu' : u⁻¹ ∈ unipRad k e := inv_mem hu
  exact (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_uniformizer_pow_of_mem_unipRad e hu i j).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_uniformizer_pow_of_mem_unipRad e hu' i j)

private theorem t2Space_localField : T2Space k := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  refine ⟨{y | valuation k y < valuation k x}, ?_, fun h => lt_irrefl (valuation k x) (by simpa using h)⟩
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  exact ⟨Units.mk0 _ ((valuation k).ne_zero_iff.2 hx), fun y hy => by simpa using hy⟩

theorem isClosed_unipRad (e : (Σ a, m a) ≃ n) : IsClosed (unipRad k e : Set (GL n k)) := by
  have : T2Space k := t2Space_localField
  have hv : Continuous fun g : GL n k => (g : Matrix n n k) := Units.continuous_val
  have hc : ∀ i j, Continuous fun g : GL n k => (g : Matrix n n k) i j := fun i j => hv.matrix_elem i j
  have hset : (unipRad k e : Set (GL n k)) =
      {g : GL n k | ∀ i j, blk e j < blk e i → (g : Matrix n n k) i j = 0} ∩
        {g : GL n k | ∀ a (i j : m a), (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipRad, mem_parab, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [hset]
  refine IsClosed.inter ?_ ?_
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (hc i j) continuous_const
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (hc _ _) continuous_const

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem eventually_mem_twKer_inf (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V} {v : V}
    (hv : v ∈ twKer π (unipRad k e) 1) :
    ∀ᶠ M : ℕ in Filter.atTop, v ∈ twKer π (grp k (conc_wt e M) ⊓ unipRad k e) 1 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, w, rfl⟩ := hx
    filter_upwards [eventually_mem_grp e u.2] with M hM
    exact Submodule.subset_span ⟨⟨u, hM, u.2⟩, w, rfl⟩
  | zero => exact Filter.Eventually.of_forall fun _ => Submodule.zero_mem _
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with M h₁ h₂
    exact Submodule.add_mem _ h₁ h₂
  | smul c x _ hx =>
    filter_upwards [hx] with M h
    exact Submodule.smul_mem _ c h

private theorem twKer_one_mono' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {H K : Subgroup G} (hHK : H ≤ K) : twKer ρ H 1 ≤ twKer ρ K 1 := by
  refine Submodule.span_mono ?_
  rintro _ ⟨h, w, rfl⟩
  exact ⟨⟨h, hHK h.2⟩, w, rfl⟩

theorem jacMap_injective (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL n k) V) (π : Representation ℂ (GL n k) W)
    (f : π₁.IntertwiningMap π) (hπ : IsSmooth π) (hf : Function.Injective f) :
    Function.Injective (jacMap e f) := by
  intro x y hxy
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hmk : ∀ u : V, jacMap e f (Submodule.Quotient.mk u) = Submodule.Quotient.mk (f u) :=
    fun _ => rfl
  rw [hmk, hmk, Submodule.Quotient.eq, ← map_sub] at hxy
  rw [Submodule.Quotient.eq]
  obtain ⟨M, hM⟩ := (eventually_mem_twKer_inf e hxy).exists
  have hcpt : IsCompact ((grp k (conc_wt e M) ⊓ unipRad k e : Subgroup (GL n k)) : Set (GL n k)) := by
    rw [Subgroup.coe_inf]
    exact (isCompact_grp (conc_wt e M)).inter_right (isClosed_unipRad e)
  exact twKer_one_mono' inf_le_right (mem_twKer_of_map f hπ hf hcpt hM)

end GlobalTheory.JacInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
section
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel Matrix

namespace GlobalTheory.SmGL.EmptyBlocks

section General

variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem jhMult_comp_surjective (φ : H →* G) (hφ : Function.Surjective φ) (σ : Representation F G W)
    (ρ : Representation F G V) :
    jhMult (σ.comp φ : Representation F H W) (ρ.comp φ : Representation F H V) = jhMult σ ρ := by
  have : ∀ r, OccursTimes (σ.comp φ : Representation F H W) (ρ.comp φ : Representation F H V) r ↔
      OccursTimes σ ρ r := fun r => by
    constructor
    · rintro ⟨S, T, h1, h2, h3⟩
      let up : Subrepresentation (ρ.comp φ : Representation F H V) → Subrepresentation ρ := fun S =>
        ⟨S.toSubmodule, fun g v hv => by
          obtain ⟨h, rfl⟩ := hφ g
          exact S.apply_mem_toSubmodule h hv⟩
      refine ⟨fun i => up (S i), fun i => up (T i), h1, h2, fun i => (h3 i).map fun ψ =>
        .mk ψ.toLinearEquiv fun g => ?_⟩
      obtain ⟨h, rfl⟩ := hφ g
      exact ψ.isIntertwining' h
    · rintro ⟨S, T, h1, h2, h3⟩
      let down : Subrepresentation ρ → Subrepresentation (ρ.comp φ : Representation F H V) := fun S =>
        ⟨S.toSubmodule, fun h v hv => S.apply_mem_toSubmodule (φ h) hv⟩
      exact ⟨fun i => down (S i), fun i => down (T i), h1, h2, fun i => (h3 i).map fun ψ =>
        .mk ψ.toLinearEquiv fun h => ψ.isIntertwining' (φ h)⟩
  simp only [jhMult, this]

end General

section Blocks

variable (R : Type) [CommRing R] {β n : Type} [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n]
  {c : β → Type} [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (f : (Σ j, c j) ≃ n)

def torusToLevi : (n → Rˣ) →* Levi R c :=
  (leviProj R f).comp ((diagT R n).codRestrict (parab R f) fun t => mem_parab.2 fun i j h => by
    rw [val_diagT, diagonal_apply_ne]
    rintro rfl
    exact lt_irrefl _ h)

theorem val_torusToLevi (t : n → Rˣ) (j : β) :
    (torusToLevi R f t j : Matrix (c j) (c j) R) = diagonal fun x => (t (f ⟨j, x⟩) : R) := by
  ext x y
  show (diagT R n t : Matrix n n R) (f ⟨j, x⟩) (f ⟨j, y⟩) = _
  rw [val_diagT]
  simp [diagonal_apply]

theorem leviEmb_torusToLevi (t : n → Rˣ) : leviEmb R f (torusToLevi R f t) = diagT R n t := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective j
  by_cases h : a = b
  · subst h
    simp [leviEmb, val_torusToLevi, val_diagT, diagonal_apply]
  · have hij : f ⟨a, i⟩ ≠ f ⟨b, j⟩ := fun h' => h (congrArg Sigma.fst (f.injective h'))
    simp [leviEmb, blockDiagonal'_apply, h, val_diagT, diagonal_apply_ne, hij]

theorem det_torusToLevi (t : n → Rˣ) (j : β) :
    GeneralLinearGroup.det (torusToLevi R f t j) = ∏ x, t (f ⟨j, x⟩) := by
  ext
  simp [val_torusToLevi]

theorem prod_det_torusToLevi (χ : β → Rˣ →* ℂˣ) (t : n → Rˣ) :
    ∏ j, χ j (GeneralLinearGroup.det (torusToLevi R f t j)) = ∏ i, χ (blk f i) (t i) := by
  rw [← f.prod_comp, Fintype.prod_sigma]
  simp [det_torusToLevi]

theorem torusToLevi_surjective (hf : Function.Injective (blk f)) :
    Function.Surjective (torusToLevi R f) := by
  intro g
  refine ⟨fun i => GeneralLinearGroup.det (g (blk f i)), funext fun j => ?_⟩
  ext x y
  have hs : ∀ u v : c j, u = v := fun u v => by
    have : f ⟨j, u⟩ = f ⟨j, v⟩ := hf (by simp)
    simpa using this
  obtain rfl := hs x y
  haveI : Unique (c j) := ⟨⟨x⟩, fun u => hs _ _⟩
  rw [val_torusToLevi, diagonal_apply_eq, blk_apply, GeneralLinearGroup.val_det_apply,
    det_unique, hs default x]


omit [LinearOrder β] [DecidableEq n] [∀ j, DecidableEq (c j)] in
theorem sum_card_blocks (P : β → Prop) [DecidablePred P] :
    ∑ b with P b, (Fintype.card (c b) : ℤ) = ∑ i with P (blk f i), (1 : ℤ) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← f.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [blk_apply]
  split_ifs <;> simp

variable [LinearOrder n]


omit [DecidableEq n] [∀ j, DecidableEq (c j)] in
theorem modExp_blk (hf : StrictMono (blk f)) (i : n) :
    modExp c (blk f i) = modExp (fun _ : n => Unit) i := by
  unfold modExp
  rw [sum_card_blocks f, sum_card_blocks f]
  simp [hf.lt_iff_lt]

theorem unipRad_eq (hf : StrictMono (blk f)) : unipRad R f = unipB R n := by
  ext g
  rw [mem_unipRad, mem_unipB, mem_parab]
  simp only [hf.lt_iff_lt]
  refine and_congr Iff.rfl ⟨fun h i => ?_, fun h a x y => ?_⟩
  · obtain ⟨⟨a, x⟩, rfl⟩ := f.surjective i
    simpa using h a x x
  · have : f ⟨a, x⟩ = f ⟨a, y⟩ := hf.injective (by simp)
    obtain rfl : x = y := by simpa using this
    simpa using h _

end Blocks

theorem jhMult_jac_eq_jacB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (β n : Type) [Fintype β] [LinearOrder β] [Fintype n]
    [DecidableEq n] [LinearOrder n] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)]
    (f : (Σ j, c j) ≃ n) (hf : StrictMono (blk f)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (χ : β → kˣ →* ℂˣ) :
    jhMult (ofChar (leviChar c χ)) (jac f π) =
      jhMult (ofChar (torusChar fun i => χ (blk f i))) (jacB π) := by
  have h1 : ((ofChar (leviChar c χ)).comp (torusToLevi k f) : Representation ℂ (n → kˣ) ℂ) =
      ofChar (torusChar fun i => χ (blk f i)) := by
    refine MonoidHom.ext fun t => LinearMap.ext fun y => ?_
    show ofChar _ _ y = _
    rw [ofChar_apply, ofChar_apply, leviChar_apply, torusChar_apply, prod_det_torusToLevi]
  have h2 : ∀ t, deltaHalf k c (torusToLevi k f t) =
      deltaHalf k (fun _ : n => Unit) (leviTorus k n t) := fun t => by
    have hd : ∀ i, GeneralLinearGroup.det (leviTorus k n t i) = t i :=
      congrFun ((leviTorus k n).left_inv t)
    rw [deltaHalf_apply, deltaHalf_apply,
      prod_det_torusToLevi k f fun a => absPow k ((modExp c a : ℂ) / 2)]
    simp only [hd, modExp_blk f hf]
  have h3 : twKer π (unipRad k f) 1 = twKer π (unipB k n) 1 := by rw [unipRad_eq k f hf]
  rw [← jhMult_comp_surjective (torusToLevi k f) (torusToLevi_surjective k f hf.injective), h1]
  refine jhMult_congr_right _ (.mk (Submodule.quotEquivOfEq _ _ h3) fun t => ?_)
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  show Submodule.quotEquivOfEq _ _ h3 (jac f π (torusToLevi k f t) (Submodule.Quotient.mk v)) =
    jac (points n) π (leviTorus k n t) (Submodule.Quotient.mk v)
  rw [jac_mk, jac_mk, map_smul, h2, leviEmb_torusToLevi]
  simp only [Submodule.quotEquivOfEq_mk]
  have heq : diagT k n t = leviEmb k (points n) (leviTorus k n t) := by
    ext i j
    rw [val_diagT]
    simp [leviEmb, leviTorus, points, GeneralLinearGroup.coe_scalar, Matrix.scalar, diagonal_apply]
  rw [heq]
  congr 4

end GlobalTheory.SmGL.EmptyBlocks
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ProjComm

theorem coeff_conj_of_central {H : Type} [Group H] (z : MonoidAlgebra ℂ H) (hz : ∀ a, z * a = a * z) (g h : H) :
    z.coeff (g * h * g⁻¹) = z.coeff h := by
  have key := congrArg (fun w => w.coeff (g * h)) (hz (MonoidAlgebra.single g 1))
  simp only [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply, mul_one, one_mul,
    inv_mul_cancel_left] at key
  exact key

theorem goodProjector_coeff_classFunction (D : D7) (g h : G0g D.nd) : D.ntypes.e0.coeff (g * h * g⁻¹) = D.ntypes.e0.coeff h := by
  unfold NTypes.e0
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  refine finsum_congr fun a => ?_
  split_ifs
  · exact Finset.prod_congr rfl fun kv _ =>
      coeff_conj_of_central _ (D.ntypes.eSer_central kv.1 _) (g kv) (h kv)
  · rfl

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem isLift_mul {g g' : G0 L.Pg L.r} {κ κ' : GA D V} (hκ : IsLevelLift V β L g κ) (hκ' : IsLevelLift V β L g' κ') :
    IsLevelLift V β L (g * g') (κ * κ') := by
  unfold IsLevelLift at hκ hκ' ⊢
  obtain ⟨h1, h2, h3⟩ := hκ
  obtain ⟨h1', h2', h3'⟩ := hκ'
  refine ⟨mul_mem h1 h1', ?_, ?_⟩
  · rw [map_mul]
    exact mul_mem h2 h2'
  · rw [map_mul, Formalism.L2.DIV.rTup_mul h2 h2', h3, h3']

theorem isLift_inv {g : G0 L.Pg L.r} {κ : GA D V} (hκ : IsLevelLift V β L g κ) :
    IsLevelLift V β L g⁻¹ κ⁻¹ := by
  unfold IsLevelLift at hκ ⊢
  obtain ⟨h1, h2, h3⟩ := hκ
  refine ⟨inv_mem h1, ?_, ?_⟩
  · rw [map_inv]
    exact inv_mem h2
  · rw [map_inv, Formalism.L2.DIV.rTup_inv h2, h3]

private theorem actG0_apply_eq_levChi_inv_mul_choose {g : G0 L.Pg L.r} (hex : ∃ κ, IsLevelLift V β L g κ) (F : GA D V → ℂ) (x : GA D V) :
    actG0 V β L g F x = (levChi V β (flagL L) hex.choose)⁻¹ * F (x * hex.choose) := by
  unfold actG0
  rw [dite_eq_left hex]

private theorem levChi_flagL_mul_of_mem_parLev {κ κ' : GA D V} (hκ : finE V κ ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L)
    (hκ' : finE V κ' ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L) :
    levChi V β (flagL L) (κ * κ') = levChi V β (flagL L) κ * levChi V β (flagL L) κ' := by
  unfold levChi
  rw [map_mul, levFn_flag_mul hκ hκ', Units.val_mul]

theorem levelGroupAction_mul_of_lifts {g g' : G0 L.Pg L.r} (hg : ∃ κ, IsLevelLift V β L g κ) (hg' : ∃ κ, IsLevelLift V β L g' κ)
    {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    actG0 V β L g (actG0 V β L g' F) = actG0 V β L (g * g') F := by
  have hex := hg
  obtain ⟨κ', hκ'⟩ := hg'
  funext x
  have hc : IsLevelLift V β L g hex.choose := hex.choose_spec
  have hm : IsLevelLift V β L (g * g') (hex.choose * κ') := isLift_mul hc hκ'
  have hpar : finE V hex.choose ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := by
    unfold IsLevelLift at hc
    exact hc.2.1
  have hpar' : finE V κ' ∈ Formalism.L2.DIV.parLev D.sp.cm V.gram β L := by
    unfold IsLevelLift at hκ'
    exact hκ'.2.1
  rw [actG0_apply_eq_levChi_inv_mul_choose hex, level_action_spec hF ⟨κ', hκ'⟩ κ' hκ' (x * hex.choose),
    level_action_spec hF ⟨_, hm⟩ _ hm x, levChi_flagL_mul_of_mem_parLev hpar hpar', mul_assoc x]
  ring

theorem levelGroupAction_eq_zero_of_no_lift {g : G0 L.Pg L.r} (hg : ¬ ∃ κ, IsLevelLift V β L g κ) (F : GA D V → ℂ) :
    actG0 V β L g F = 0 := by
  unfold actG0
  exact dif_neg hg

theorem actL_conj (g h : G0 L.Pg L.r) {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    actL V β L (g * h * g⁻¹) (actL V β L g F) = actL V β L g (actL V β L h F) := by
  show actG0 V β L (g * h * g⁻¹) (actG0 V β L g F) = actG0 V β L g (actG0 V β L h F)
  by_cases hg : ∃ κ, IsLevelLift V β L g κ
  · obtain ⟨κ, hκ⟩ := hg
    by_cases hh : ∃ κ, IsLevelLift V β L h κ
    · obtain ⟨μ, hμ⟩ := hh
      have hc : ∃ κ, IsLevelLift V β L (g * h * g⁻¹) κ :=
        ⟨κ * μ * κ⁻¹, isLift_mul (isLift_mul hκ hμ) (isLift_inv hκ)⟩
      rw [levelGroupAction_mul_of_lifts hc ⟨κ, hκ⟩ hF, levelGroupAction_mul_of_lifts ⟨κ, hκ⟩ ⟨μ, hμ⟩ hF, inv_mul_cancel_right]
    · have hc : ¬ ∃ κ, IsLevelLift V β L (g * h * g⁻¹) κ := by
        rintro ⟨ν, hν⟩
        apply hh
        have hl := isLift_mul (isLift_mul (isLift_inv hκ) hν) hκ
        rw [show g⁻¹ * (g * h * g⁻¹) * g = h by group] at hl
        exact ⟨_, hl⟩
      rw [levelGroupAction_eq_zero_of_no_lift hc, levelGroupAction_eq_zero_of_no_lift hh]
      exact (map_zero (actL V β L g)).symm
  · rw [levelGroupAction_eq_zero_of_no_lift hg F, levelGroupAction_eq_zero_of_no_lift hg (actG0 V β L h F)]
    exact map_zero (actL V β L (g * h * g⁻¹))

theorem gaL_comm {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)
    (hc : ∀ g h, c (g * h * g⁻¹) = c h) (g : G) {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    gaL V β L eG c (actL V β L (eG g) F) = actL V β L (eG g) (gaL V β L eG c F) := by
  unfold gaL
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun y => ?_).symm
  show c y • actL V β L (eG g) (actL V β L (eG y) F) =
    c (g * y * g⁻¹) • actL V β L (eG (g * y * g⁻¹)) (actL V β L (eG g) F)
  rw [hc, map_mul, map_mul, map_inv, actL_conj _ _ hF]

theorem proj_comm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.grp_record → (∀ g F, HasType (Yc D 0) (R.βY 0) (R.dat0 R.triv) F → R.e0 (actL _ (R.βY 0) (R.dat0 R.triv) (R.eG g) F) = actL _ (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.e0 F)) ∧ ∀ i σ g F, HasType (Wc D i) (R.βW i) (R.datWp i R.triv) F → R.eWf i σ (actL _ (R.βW i) (R.datWp i R.triv) (R.eG g) F) = actL _ (R.βW i) (R.datWp i R.triv) (R.eG g) (R.eWf i σ F) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ hrec
  obtain ⟨eR, plg, iso, he, -, -⟩ := hrec
  have hcls : ∀ a b : G, (idemOf A.X).coeff (a * b * a⁻¹) = (idemOf A.X).coeff b := fun a b =>
    D.what₂.embLL.injective (by rw [he, he, map_mul eR, map_mul eR, map_inv eR, goodProjector_coeff_classFunction])
  have hcl : ∀ (σ : D.what₂.LL →+* ℂ) (a b : G),
      RealDat.eC (A := A) σ (a * b * a⁻¹) = RealDat.eC (A := A) σ b := fun σ a b => by
    unfold RealDat.eC
    rw [hcls]
  refine ⟨fun g F hF => ?_, fun i σ g F hF => ?_⟩
  · exact gaL_comm (L := R.dat0 R.triv) R.eG _ (hcl _) g hF
  · exact gaL_comm (L := R.datWp i R.triv) R.eG _ (hcl σ) g hF

end GlobalTheory.ProjComm

end
end

