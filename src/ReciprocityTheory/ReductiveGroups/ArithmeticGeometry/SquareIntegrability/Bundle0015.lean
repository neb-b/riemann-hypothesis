module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.QuotientTorusMinimumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.NstatementOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.MemSpanBn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.ETSymmApply
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.MemSpanMap

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ActOmegaExpand
section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

lemma act_omega_expand {dim : (E →+* ℂ) → ℕ} (ω : Fin (Module.finrank ℚ E) → 𝓞 E)
    (hω : LinearIndependent ℚ (fun j => (ω j : E))) (α : 𝓞 E) (y : Vsp dim) :
    act α y ∈ Submodule.span ℝ (Set.range fun j => act (ω j) y) := by
  classical
  have hsp : Submodule.span ℚ (Set.range fun j => (ω j : E)) = ⊤ :=
    by
      first
      | exact hω.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)
      | (haveI : Nonempty (Fin (Module.finrank ℚ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
         exact hω.span_eq_top_of_card_eq_finrank (Fintype.card_fin _))
  have hα : (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E)) := by
    rw [hsp]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℚ E) → ℚ, ∑ j, c j • (ω j : E) = α := by
    first
    | exact (Submodule.mem_span_range_iff_exists_fun ℚ).1 hα
    | exact Submodule.mem_span_range_iff_exists_fun.1 hα
  have key : act α y = ∑ j, ((c j : ℝ)) • act (ω j) y := by
    ext i
    simp only [act, ← hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Rat.smul_def, map_mul, map_ratCast, Finset.sum_mul, Complex.real_smul, mul_assoc]
  rw [key]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

lemma rank_bound {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim))
    (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖)
    (hact : ∀ (α : 𝓞 E) u, u ∈ Xg L I → act α u ∈ Xg L I)
    (ω : Fin (Module.finrank ℚ E) → 𝓞 E) (hω : LinearIndependent ℚ (fun j => (ω j : E)))
    (σ : E →+* ℂ) (b : Set (Vsp dim)) [Fintype b] (hb : b ⊆ prj σ '' (Xg L I))
    (hli : LinearIndependent ℂ (fun s : b => (s : Vsp dim))) :
    Module.finrank ℚ E * Fintype.card b ≤ Module.finrank ℝ (IR I) := by
  classical
  have hpre : ∀ s : b, ∃ u, u ∈ Xg L I ∧ prj σ u = (s : Vsp dim) := by
    intro s
    obtain ⟨u, hu, h⟩ := hb s.2
    exact ⟨u, hu, h⟩
  choose u hu hus using hpre
  let v : Fin (Module.finrank ℚ E) × b → Vsp dim := fun p => act (ω p.1) (u p.2)
  have hvX : ∀ p, v p ∈ Xg L I := fun p => hact _ _ (hu p.2)
  have hvIR : ∀ p, v p ∈ IR I := by
    intro p
    have h : ∃ x ∈ L, IsU I x (v p) := hvX p
    obtain ⟨x, _, hx⟩ := h
    exact hx.1
  have hprj : ∀ (α : 𝓞 E) (w : Vsp dim), prj σ (act α w) = σ (α : E) • prj σ w := by
    intro α w
    ext i
    by_cases h : i.1 = σ
    · simp [prj, act_apply, h]
    · simp [prj, h]

  have hZ : ∀ m : Fin (Module.finrank ℚ E) × b → ℤ, ∑ p, m p • v p = 0 → ∀ p, m p = 0 := by
    intro m hm
    have h1 : ∑ s : b, (∑ j, ((m (j, s) : ℂ) * σ (ω j : E))) • (s : Vsp dim) = 0 := by
      have := congrArg (prj σ) hm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at this
      rw [← this, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      show _ = prj σ (m (j, s) • act (ω j) (u s))
      rw [map_zsmul, hprj, hus, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    rintro ⟨j, s⟩
    have h2 := Fintype.linearIndependent_iff.mp hli
      (fun s => ∑ j, ((m (j, s) : ℂ) * σ (ω j : E))) h1 s
    have h3 : σ (∑ j, ((m (j, s) : E)) * (ω j : E)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; simpa [map_mul, map_intCast] using h2
    have h4 : ∑ j, ((m (j, s) : ℚ)) • (ω j : E) = 0 := by
      have h5 := (map_eq_zero_iff σ σ.injective).mp h3
      simpa [Rat.smul_def] using h5
    have h6 := Fintype.linearIndependent_iff.mp hω (fun j => (m (j, s) : ℚ)) h4 j
    exact_mod_cast h6

  have hR : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc p
    by_contra hcp
    let y : ℕ → Vsp dim := fun k => -(∑ q, ⌊(k : ℝ) * c q⌋ • v q)
    have hyX : ∀ k, y k ∈ Xg L I := fun k =>
      neg_mem (sum_mem fun q _ => zsmul_mem (hvX q) _)
    have hyeq : ∀ k : ℕ, y k = ∑ q, Int.fract ((k : ℝ) * c q) • v q := by
      intro k
      have h0 : ∑ q, ((k : ℝ) * c q) • v q = 0 := by
        simp_rw [mul_smul]
        rw [← Finset.smul_sum, hc, smul_zero]
      simp only [y, Int.fract, sub_smul, Finset.sum_sub_distrib, h0, zero_sub]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      exact (Int.cast_smul_eq_zsmul ℝ _ _).symm
    have hyn : ∀ k, ‖y k‖ ≤ ∑ q, ‖v q‖ := by
      intro k
      rw [hyeq]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    have hfin : {x | x ∈ (Xg L I : Set (Vsp dim)) ∧ ‖x‖ ≤ ∑ q, ‖v q‖}.Finite :=
      finite_sep _ (sep_of_group (Xg L I) hsep _ subset_rfl) _
    let g : ℕ → (Fin (Module.finrank ℚ E) × b → ℤ) := fun k q => ⌊(k : ℝ) * c q⌋
    let Φ : (Fin (Module.finrank ℚ E) × b → ℤ) → Vsp dim := fun m => -(∑ q, m q • v q)
    have hΦ : Function.Injective Φ := by
      intro m m' h
      have h' : ∑ q, m q • v q = ∑ q, m' q • v q := neg_inj.mp h
      have h'' : ∑ q, (m q - m' q) • v q = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, h', sub_self]
      funext q
      exact sub_eq_zero.mp (hZ _ h'' q)
    have hrg : (Set.range g).Finite := by
      refine Set.Finite.of_finite_image ?_ hΦ.injOn
      refine hfin.subset ?_
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨hyX k, hyn k⟩
    have hrp : (Set.range fun k : ℕ => ⌊(k : ℝ) * c p⌋).Finite :=
      (hrg.image (fun m => m p)).subset (by rintro _ ⟨k, rfl⟩; exact ⟨g k, ⟨k, rfl⟩, rfl⟩)
    obtain ⟨B, hB⟩ := hrp.bddAbove
    obtain ⟨B', hB'⟩ := hrp.bddBelow
    have hcpos : 0 < |c p| := abs_pos.mpr hcp
    obtain ⟨k, hk⟩ := exists_nat_gt ((|(B : ℝ)| + |(B' : ℝ)| + 2) / |c p|)
    have hkc : |(B : ℝ)| + |(B' : ℝ)| + 2 < (k : ℝ) * |c p| := by
      rwa [div_lt_iff₀ hcpos] at hk
    have hup : ⌊(k : ℝ) * c p⌋ ≤ B := hB ⟨k, rfl⟩
    have hlo : B' ≤ ⌊(k : ℝ) * c p⌋ := hB' ⟨k, rfl⟩
    have h1 : (k : ℝ) * c p - 1 < (⌊(k : ℝ) * c p⌋ : ℝ) := Int.sub_one_lt_floor _
    have h2 : (⌊(k : ℝ) * c p⌋ : ℝ) ≤ (k : ℝ) * c p := Int.floor_le _
    have hup' : (⌊(k : ℝ) * c p⌋ : ℝ) ≤ B := by exact_mod_cast hup
    have hlo' : (B' : ℝ) ≤ ⌊(k : ℝ) * c p⌋ := by exact_mod_cast hlo
    have hB0 := abs_nonneg (B : ℝ)
    have hB'0 := abs_nonneg (B' : ℝ)
    rcases lt_or_gt_of_ne hcp with hneg | hpos
    · rw [abs_of_neg hneg, mul_neg] at hkc
      have := neg_abs_le (B' : ℝ)
      linarith
    · rw [abs_of_pos hpos] at hkc
      have := le_abs_self (B : ℝ)
      linarith
  have hw : LinearIndependent ℝ (fun p => (⟨v p, hvIR p⟩ : IR I)) :=
    LinearIndependent.of_comp (IR I).subtype hR
  have := hw.fintype_card_le_finrank
  simpa [Fintype.card_prod, Fintype.card_fin] using this

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IKDiscrete
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

def IK {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) : Submodule ℤ (IR I) :=
  I.comap ((IR I).subtype.toAddMonoidHom.toIntLinearMap)

theorem mem_IK {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x : IR I} :
    x ∈ IK I ↔ (x : Vsp dim) ∈ I := Iff.rfl

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem IK_discrete (hI : IsSplit P I) : DiscreteTopology (IK I) := by
  let f : IK I → X.L := fun x => ⟨((x : IR I) : Vsp X.dim), hI.le (mem_IK.1 x.2)⟩
  have hc : Continuous f :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  exact DiscreteTopology.of_continuous_injective hc hinj

theorem IK_span : Submodule.span ℝ (IK I : Set (IR I)) = ⊤ := by
  apply Submodule.map_injective_of_injective (IR I).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  show _ = Submodule.span ℝ (I : Set (Vsp X.dim))
  congr 1
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mem_IK.1 hz
  · intro hy
    exact ⟨⟨y, Submodule.subset_span hy⟩, mem_IK.2 hy, rfl⟩

def Ib (hI : IsSplit P I) : Module.Basis (Fin (Module.finrank ℝ (IR I))) ℝ (IR I) :=
  haveI := IK_discrete hI
  haveI : IsZLattice ℝ (IK I) := ⟨IK_span⟩
  haveI := ZLattice.module_free ℝ (IK I)
  (Module.Basis.ofZLatticeBasis ℝ (IK I) (Module.Free.chooseBasis ℤ (IK I))).reindex
    (Fintype.equivFinOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ]))

theorem Ib_span (hI : IsSplit P I) : Submodule.span ℤ (Set.range (Ib hI)) = IK I := by
  unfold Ib
  rw [Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]

theorem Ib_mem (hI : IsSplit P I) (i : Fin (Module.finrank ℝ (IR I))) :
    ((Ib hI i : IR I) : Vsp X.dim) ∈ I := by
  have h : Ib hI i ∈ IK I := by
    rw [← Ib_span hI]
    exact Submodule.subset_span (Set.mem_range_self i)
  exact mem_IK.1 h

theorem Ib_det_ne (hI : IsSplit P I) : (Col.ob (IR I)).toBasis.det (Ib hI) ≠ 0 := ((Module.Basis.is_basis_iff_det _).1 ⟨(Ib hI).linearIndependent, (Ib hI).span_eq⟩).ne_zero

def zmG (I : Submodule ℤ (Vsp X.dim)) (s : (Fin 1 → Vsp X.dim) → ℂ) (v : Vsp X.dim) : ℂ :=
  s (fun _ => v) * Complex.exp (-(Real.pi / 2) * Col.S (IR I) v)

def zmBox (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}

def zmC (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) (n : Fin (Module.finrank ℝ (IR I)) → ℤ)
    (v : Vsp X.dim) : ℂ :=
  ∫ t in zmBox (Module.finrank ℝ (IR I)),
    Complex.exp (-(2 * Real.pi * Complex.I * ∑ i, (n i : ℂ) * (t i : ℂ))) *
      zmG I s (v + ∑ i, t i • ((Ib hI i : IR I) : Vsp X.dim))

def zmB (hI : IsSplit P I) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ :=
  fun t => zmC hI s 0 (Col.jj (IR I) t)

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IteratedDerivListBound
section
namespace ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ}

section Col
variable {dim : (E →+* ℂ) → ℕ}

theorem iteratedDeriv_list_bound (s : (Fin 1 → Vsp dim) → ℂ) (c : ℕ) (μ : ℂ) (y : Vsp dim) (ε : ℝ)
    (σ : E →+* ℂ)
    (hbd : ∀ xs : Fin c → Vsp dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
      ‖d1 s c xs - μ * ∏ k, Hf (xs k) y‖ ≤ ε)
    (l : List (Vsp dim)) (g : Fin c → Vsp dim)
    (hl : (l : Multiset (Vsp dim)) = Multiset.map g Finset.univ.val)
    (hg : ∀ r, InPart σ (g r) ∧ ‖g r‖ = 1) :
    ‖d1 s l.length (fun j => l.get j) - μ * ∏ r, Hf (g r) y‖ ≤ ε := by
  have hlen : l.length = c := by
    have := congrArg Multiset.card hl
    simpa using this
  subst hlen
  have hmem : ∀ j : Fin l.length, InPart σ (l.get j) ∧ ‖l.get j‖ = 1 := by
    intro j
    have : l.get j ∈ Multiset.map g Finset.univ.val := by
      rw [← hl]; exact Multiset.mem_coe.2 (List.get_mem l j)
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.1 this
    rw [← hr]; exact hg r
  have hm : Finset.univ.val.map (fun j : Fin l.length => l.get j) = (l : Multiset (Vsp dim)) := by
    rw [Fin.univ_val_map]
    congr 1
    first
    | exact List.ofFn_get l
    | exact List.ofFn_getElem l
    | simp
  have hprod : ∏ j : Fin l.length, Hf (l.get j) y = ∏ r, Hf (g r) y := by
    calc ∏ j : Fin l.length, Hf (l.get j) y
        = ((Finset.univ.val.map (fun j : Fin l.length => l.get j)).map (fun x => Hf x y)).prod := by
          rw [Multiset.map_map]; rfl
      _ = ∏ r, Hf (g r) y := by
          rw [hm, hl, Multiset.map_map]; rfl
  have := hbd (fun j => l.get j) hmem
  rw [hprod] at this
  exact this

theorem d1_zero (s : (Fin 1 → Vsp dim) → ℂ) (v : Fin 0 → Vsp dim) : d1 s 0 v = s 0 := by
  unfold d1
  exact iteratedFDeriv_zero_apply _

end Col

section Main
variable {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim)

open Classical in
def eU (j : Fin nb) (a : Fin (bs j).i) : Vsp dim := by
  classical
  exact EuclideanSpace.single (⟨(bs j).τ, Fin.castLE (bs j).hi a⟩ : Idx dim) (1 : ℂ)

def idealA (μ : (Σ j : Fin nb, Fin (bs j).i) → ℂ) (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim)
    (ee : Fin n → ℂ) (T : Choice bs) (k : Fin n) : ℂ :=
  match owner bs k with
  | some p => μ p * ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p)
  | none => ee k

def blockM (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim) (j : Fin nb) :
    Matrix (Fin (bs j).i) (Fin (bs j).i) ℂ :=
  Matrix.of fun a b => Hf (eU bs j a) (y ⟨j, b⟩)

theorem main_term (hD : Disj bs) (μ : (Σ j : Fin nb, Fin (bs j).i) → ℂ)
    (y : (Σ j : Fin nb, Fin (bs j).i) → Vsp dim) (ee : Fin n → ℂ) :
    ∑ T : Choice bs, sgnT bs T * ∏ k, idealA bs μ y ee T k =
      (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) * (∏ p, μ p) *
        ∏ j, (blockM bs y j).det ^ (bs j).c := by
  have hinj : Function.Injective (colB bs) := by
    rintro ⟨j, a⟩ ⟨j', a'⟩ h
    simp only [colB] at h
    by_cases hj : j = j'
    · subst hj
      have := (bs j).col_inj h
      subst this
      rfl
    · exact absurd h (hD j j' hj a a')
  have hown : ∀ p, owner bs (colB bs p) = some p := by
    intro p
    have hex : ∃ p', colB bs p' = colB bs p := ⟨p, rfl⟩
    unfold owner
    rw [dite_eq_left hex]
    exact congrArg some (hinj hex.choose_spec)
  have hnone : ∀ k, owner bs k = none ↔ k ∉ Finset.univ.image (colB bs) := by
    intro k
    constructor
    · intro h hk
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hk
      rw [hown] at h
      exact Option.some_ne_none _ h
    · intro h
      unfold owner
      rw [dite_eq_right]
      rintro ⟨p, rfl⟩
      exact h (Finset.mem_image_of_mem _ (Finset.mem_univ p))
  have hT : ∀ T : Choice bs, ∏ k, idealA bs μ y ee T k =
      (∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) *
        ∏ p, (μ p * ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p)) := by
    intro T
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => owner bs k = none)]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      have h := (Finset.mem_filter.mp hk).2
      simp only [idealA, h]
    · have hset : Finset.univ.filter (fun k => ¬ owner bs k = none) = Finset.univ.image (colB bs) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hnone]
        exact not_not
      rw [hset, Finset.prod_image (fun p _ q _ h => hinj h)]
      refine Finset.prod_congr rfl fun p _ => ?_
      simp only [idealA, hown]
  have hdet : ∀ j, (blockM bs y j).det ^ (bs j).c =
      ∏ r : Fin (bs j).c, ∑ σ : Equiv.Perm (Fin (bs j).i),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ b, Hf (eU bs j (σ b)) (y ⟨j, b⟩) := by
    intro j
    rw [Fin.prod_const, Matrix.det_apply]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    rfl
  have hsum : ∑ T : Choice bs, sgnT bs T * ∏ p, ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p) =
      ∏ j, (blockM bs y j).det ^ (bs j).c := by
    simp_rw [hdet]
    first
    | simp_rw [Fintype.prod_sum]
    | simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [Finset.prod_mul_distrib, sgnT]
    congr 1
    first
    | rw [Fintype.prod_sigma]
    | rw [← Finset.univ_sigma_univ, Finset.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    first
    | rw [Finset.prod_comm]
    | exact Finset.prod_comm.symm
  calc ∑ T, sgnT bs T * ∏ k, idealA bs μ y ee T k
      = ∑ T : Choice bs, ((∏ k ∈ Finset.univ.filter (fun k => owner bs k = none), ee k) * ∏ p, μ p) *
          (sgnT bs T * ∏ p, ∏ r, Hf (eU bs p.1 (T p.1 r p.2)) (y p)) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [hT, Finset.prod_mul_distrib]
        ring
    _ = _ := by rw [← Finset.mul_sum, hsum]

end Main

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitC
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem sq_le_Qy_of_le_firstMinimum (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (hne : x ≠ 0) : X.la1 ≤ ‖x‖ := by
  unfold PT.la1
  apply csInf_le
  · exact ⟨0, fun t ht => by obtain ⟨y, -, -, rfl⟩ := ht; exact norm_nonneg y⟩
  · exact ⟨x, hx, hne, rfl⟩

theorem exists_short (X : PT E) (hne : ∃ x ∈ X.L, x ≠ 0) {t : ℝ} (h : X.la1 < t) :
    ∃ x ∈ X.L, x ≠ 0 ∧ ‖x‖ < t := by
  unfold PT.la1 at h
  obtain ⟨x, hx, hne'⟩ := hne
  obtain ⟨s, ⟨y, hy, hy0, rfl⟩, hs⟩ := exists_lt_of_csInf_lt (s := {t : ℝ | ∃ x ∈ X.L, x ≠ 0 ∧ t = ‖x‖}) ⟨‖x‖, x, hx, hne', rfl⟩ h
  exact ⟨y, hy, hy0, hs⟩

theorem first_minimum_pos (X : PT E) (hne : ∃ x ∈ X.L, x ≠ 0) : 0 < X.la1 := by
  obtain ⟨x0, hx0, hx0ne⟩ := hne
  have hfin : Set.Finite {y : Vsp X.dim | y ∈ X.L ∧ y ≠ 0 ∧ ‖y‖ ≤ ‖x0‖} := by
    apply (ZSpan.setFinite_inter X.b (Metric.isBounded_closedBall (x := (0 : Vsp X.dim))
      (r := ‖x0‖))).subset
    rintro y ⟨hy, -, hyn⟩
    exact ⟨mem_closedBall_zero_iff.2 hyn, hy⟩
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image hfin.toFinset (fun y => ‖y‖)
    ⟨x0, (Set.Finite.mem_toFinset hfin).2 ⟨hx0, hx0ne, le_rfl⟩⟩
  rw [Set.Finite.mem_toFinset] at hm
  obtain ⟨-, hm0, hmle⟩ := hm
  have hpos : 0 < ‖m‖ := norm_pos_iff.2 hm0
  refine lt_of_lt_of_le hpos ?_
  unfold PT.la1
  refine le_csInf ⟨‖x0‖, x0, hx0, hx0ne, rfl⟩ ?_
  rintro t ⟨y, hy, hy0, rfl⟩
  by_cases hyle : ‖y‖ ≤ ‖x0‖
  · exact hmin y ((Set.Finite.mem_toFinset hfin).2 ⟨hy, hy0, hyle⟩)
  · exact le_trans hmle (le_of_lt (not_le.1 hyle))

theorem L_ne_zero (X : PT E) (hr : 1 ≤ X.r) (τ : E →+* ℂ) : ∃ x ∈ X.L, x ≠ 0 := by
  have hpos : 0 < Fintype.card (Idx X.dim) := by
    have h := X.dim_conj τ
    rw [Fintype.card_pos_iff]
    by_cases h0 : 0 < X.dim τ
    · exact ⟨⟨τ, ⟨0, h0⟩⟩⟩
    · exact ⟨⟨NumberField.ComplexEmbedding.conjugate τ, ⟨0, by omega⟩⟩⟩
  exact ⟨X.b ⟨0, by omega⟩, Submodule.subset_span (Set.mem_range_self _), X.b.ne_zero _⟩

theorem sat_of_IR {X : PT E} {I : Submodule ℤ (Vsp X.dim)} (hs : ∀ x ∈ X.L, x ∈ IR I → x ∈ I) :
    ∀ x ∈ X.L, ∀ k : ℤ, k ≠ 0 → k • x ∈ I → x ∈ I := by
  intro x hx k hk hkx
  apply hs x hx
  have h1 : (k • x : Vsp X.dim) ∈ IR I := Submodule.subset_span hkx
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have h2 : x = (k : ℝ)⁻¹ • (k • x) := by
    rw [← Int.cast_smul_eq_zsmul ℝ, inv_smul_smul₀ hk']
  rw [h2]
  exact Submodule.smul_mem _ _ h1

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TBNFinal
section
theorem ReciprocityTheory.ChartRestriction.G.I2.thetaBasis_holds : ReciprocityTheory.ChartRestriction.G.I2.NStatement :=
  ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.nstatement_of ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepT ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepI ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepF ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepP ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepPos ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepDual ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepK
    ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepD
end

