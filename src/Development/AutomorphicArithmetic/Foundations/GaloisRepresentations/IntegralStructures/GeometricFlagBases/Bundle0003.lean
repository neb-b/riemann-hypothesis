module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.Bundle0001
public import Development.EtaleCohomology.EtaleTrace.Bundle0008
public import Development.EtaleCohomology.WeilConjectures.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.EqZeroOfLowBlk
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Int.Geo

private def blk (k : Type) [Field k] {d : ℕ} (c : Fin d → ℕ) (i : ℕ) : Submodule k (Fin d → k) where
  carrier := {v | ∀ j, c j ≠ i → v j = 0}
  zero_mem' _ _ := rfl
  add_mem' ha hb j h := by simp [ha j h, hb j h]
  smul_mem' r v hv j h := by simp [hv j h]

theorem grSS_of :
    GrHom → SSOfSum → GrSS := by
  intro _ hSS Γ k _ _ d ρ₀ ρ c hJH hρ
  obtain ⟨hinv, hmax⟩ := hJH
  have key : ∀ (g : Γ) (i : ℕ) (u : Fin d → k), u ∈ blk k c i → ∀ a,
      (↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec u a =
        if c a = i then (↑(ρ₀ g) : Matrix (Fin d) (Fin d) k).mulVec u a else 0 := by
    intro g i u hu a
    simp only [Matrix.mulVec, dotProduct, hρ]
    split_ifs with h
    · refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h'
      · rfl
      · simp [hu b (by omega)]
    · refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with h'
      · simp [hu b (by omega)]
      · simp
  have hblk : ∀ i, IsInv ρ (blk k c i) := by
    intro i g u hu j hj
    rw [key g i u hu j, if_neg hj]
  have hsup : ⨆ i, blk k c i = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun j _ => ?_
    refine Submodule.mem_iSup_of_mem (c j) ?_
    intro a ha
    rw [Pi.single_eq_of_ne]
    rintro rfl
    exact ha rfl
  refine hSS Γ k d ρ (fun i => blk k c i) hblk ?_ hsup
  intro i U hU hUle
  have hlow : low k c i ≤ low k c (i + 1) := fun v hv j hj => hv j (by omega)
  have hblkle : blk k c i ≤ low k c (i + 1) := fun v hv j hj => hv j (by omega)
  have hdisj : ∀ v, v ∈ blk k c i → v ∈ low k c i → v = 0 := by
    intro v h1 h2
    funext j
    by_cases h : c j = i
    · exact h2 j h.ge
    · exact h1 j h
  have hU'inv : IsInv ρ₀ (low k c i ⊔ U) := by
    intro g v hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
    rw [Matrix.mulVec_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hinv i g w hw)) ?_
    have huB := hUle hu
    rw [← sub_add_cancel ((↑(ρ₀ g) : Matrix (Fin d) (Fin d) k).mulVec u)
      ((↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec u)]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (hU g u hu))
    intro a ha
    rw [Pi.sub_apply, key g i u huB a]
    split_ifs with h
    · exact sub_self _
    · rw [hinv (i + 1) g u (hblkle huB) a (by omega), sub_zero]
  rcases hmax i _ hU'inv le_sup_left (sup_le hlow (hUle.trans hblkle)) with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have hv' : v ∈ low k c i := by
      rw [← h]
      exact Submodule.mem_sup_right hv
    exact hdisj v (hUle hv) hv'
  · right
    apply le_antisymm hUle
    intro v hv
    have hv' : v ∈ low k c i ⊔ U := by
      rw [h]
      exact hblkle hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv'
    have hwB : w ∈ blk k c i := by
      have := Submodule.sub_mem _ hv (hUle hu)
      simpa using this
    rw [hdisj w hwB hw, zero_add]
    exact hu

end UpperTheory.Gal.Int.Geo
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCompSum
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.compSum_of :
    CompSum := by
  intro k _ X p hs hpr
  haveI := hs
  haveI := hpr
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : GlobalTheory.IsNormalScheme X := LateralTheory.EtaleTrace.LFinCut.normal_of_smooth p
  haveI : CompactSpace X :=
    ⟨by simpa using QuasiCompact.isCompact_preimage (f := p) Set.univ isOpen_univ isCompact_univ⟩
  haveI : IsNoetherian X := {}
  haveI : Finite (irreducibleComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  let e := Finite.equivFin (irreducibleComponents X)
  have hopen : ∀ Z : irreducibleComponents X, IsOpen (Z : Set X) :=
    fun Z => (GlobalTheory.IsNormalScheme.component Z).isOpen
  refine ⟨Nat.card (irreducibleComponents X), fun s => (GlobalTheory.IsNormalScheme.component (e.symm s) : Scheme),
    fun s => (GlobalTheory.IsNormalScheme.component (e.symm s)).ι, ⟨fun s => inferInstance, ?_, ?_⟩, ?_⟩
  · intro x
    refine ⟨e ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
    rw [Scheme.Opens.range_ι, Equiv.symm_apply_apply]
    exact mem_irreducibleComponent
  · intro s s' hss'
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    have hne : e.symm s ≠ e.symm s' := fun h => hss' (e.symm.injective h)
    show Disjoint ((e.symm s : Set X)) ((e.symm s' : Set X))
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hn
    apply hne
    have h12 : ((e.symm s : Set X)) ⊆ (e.symm s' : Set X) :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen (e.symm s).2.1.isPreirreducible
        (hopen (e.symm s')) hn).trans
        (closure_minimal Set.inter_subset_right (isClosed_of_mem_irreducibleComponents _ (e.symm s').2))
    exact Subtype.ext (le_antisymm h12 ((e.symm s).2.2 (e.symm s').2.1 h12))
  · intro s
    haveI : IsReduced X := by
      haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
        obtain ⟨hd, -⟩ := ‹GlobalTheory.IsNormalScheme X›
        haveI := hd x
        infer_instance
      exact isReduced_of_isReduced_stalk X
    haveI : IrreducibleSpace ((GlobalTheory.IsNormalScheme.component (e.symm s) : X.Opens) : Set X) :=
      Subtype.irreducibleSpace (e.symm s).2.1
    exact isIntegral_of_irreducibleSpace_of_isReduced _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PContGL
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.contGL_of :
    ContGL := by
  intro Γ k _ _ _ _ _ _ d ρ
  constructor
  · intro hρ i j
    exact (Units.continuous_val.comp hρ).matrix_elem i j
  · intro h
    have hval : Continuous fun g : Γ => ((ρ g : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) :=
      continuous_matrix h
    rw [Units.continuous_iff]
    refine ⟨hval, ?_⟩
    have hinv : (fun g : Γ => (((ρ g)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)) =
        fun g => ((ρ g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) := by
      funext g
      rw [map_inv]
    rw [hinv]
    exact hval.comp continuous_inv
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PDegCont
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.degCont_of :
    StabOpen → DegCont := by
  intro hst l _ k Ω _ _ _ _ X p hqc hqs n i hfin v μ
  have habs := LateralTheory.EWeil.AbsContPf.AbsCont_of LateralTheory.EWeil.ChevPf.Chev_of
  have key : ∀ (φ : Hl l (sch.obj (geom Ω p)) n i →ₗ[ℤ_[l]] ℚ_[l]) (x : Hl l (sch.obj (geom Ω p)) n i),
      Continuous fun σ : Gal(Ω/k) => φ (galHl l Ω p n i σ x) := by
    intro φ x
    refine habs l Gal(Ω/k) (Hl l (sch.obj (geom Ω p)) n i) (galHl l Ω p n i)
      (fun m => LinearMap.ker (LateralTheory.EWeil.ContinCut.evk l (sch.obj (geom Ω p)) n i m))
      (LateralTheory.EWeil.ContinCut.evk_anti l _ n i) ?_ ?_ φ x
    · intro y hy
      apply Subtype.ext
      funext m
      simpa [LateralTheory.EWeil.ContinCut.evk] using hy m
    · intro y m
      have hset : {σ : Gal(Ω/k) | (galHl l Ω p n i σ) y - y ∈
          LinearMap.ker (LateralTheory.EWeil.ContinCut.evk l (sch.obj (geom Ω p)) n i m)} =
          {σ | (galHl l Ω p n i σ y).1 m = y.1 m} := by
        ext σ
        simp [LateralTheory.EWeil.ContinCut.evk, sub_eq_zero]
      rw [hset]
      exact hst l k Ω p hqc hqs n i y m
  induction v using TensorProduct.induction_on with
  | zero => simpa using continuous_const
  | tmul q x =>
    have hφ := key ((μ.restrictScalars ℤ_[l]) ∘ₗ (TensorProduct.mk ℤ_[l] ℚ_[l] _ 1)) x
    refine (Continuous.mul (continuous_const : Continuous fun _ : Gal(Ω/k) => q) hφ).congr ?_
    intro σ
    have e : galHQ l Ω p n i σ (q ⊗ₜ x) = q • ((1 : ℚ_[l]) ⊗ₜ (galHl l Ω p n i σ x)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [GlobalTheory.EtC.galHQ]
    rw [e, map_smul, smul_eq_mul]
    rfl
  | add a b ha hb =>
    exact (ha.add hb).congr fun σ => by simp only [map_add (f := _), Pi.add_apply]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PDegFin
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.degFin_of :
    KunnethLefschetz.QDual → CrystallineSemistableComparison.InSum → A9 → KunnethLefschetz.ProjBC → KunnethLefschetz.SumCl → KunnethLefschetz.SumHl → KunnethLefschetz.PiBC → RelDim → CompSum → DegFin := by
  intro hQ hS a9 h1 h2 h5 h6 hR hC l _ k _ _ hk X p hp hproj
  have hprop : IsProper p := h1.2 _ p hproj
  obtain ⟨r, Y, j, hj, hY⟩ := hC k p hp hprop
  have hsm : ∀ s, Smooth (j s ≫ p) := fun s => by
    have := hj.1 s
    infer_instance
  choose d hd using fun s => hR k (j s ≫ p) (hsm s) (hY s)
  have hD : ∀ s, KunnethLefschetz.Dual l (d s) (Y s) := fun s => by
    have := hj.1 s
    have := h2 j hj s
    refine hQ l k hk (d s) (j s ≫ p) ⟨inferInstance, hd s⟩ ?_ (hY s)
    obtain ⟨N, i, hi, e⟩ := hproj
    exact ⟨N, j s ≫ i, inferInstance, by rw [Category.assoc]; exact congrArg (j s ≫ ·) e⟩
  have hb := fun n : ℤ => KunnethLefschetz.sumQ (l := l) h5 h6 hS j hj n
  refine ⟨fun n => ?_, ((2 * Finset.univ.sup d : ℕ) : ℤ), fun n hn => ?_⟩
  · have := fun s => (hD s).1 n
    exact FiniteDimensional.of_injective (LinearMap.pi fun s => LateralTheory.EtaleTrace.pb l (j s) n) (hb n).1
  · rcases hn with hn | hn
    · have hs : ∀ i, Subsingleton (HtL l i (sch.obj X) n 0) := fun i =>
        (a9 (ZMod (l ^ i)) (tw (l ^ i) 0)).1 _ n hn
      have : Subsingleton (Hl l (sch.obj X) n 0) :=
        ⟨fun a b => Subtype.ext (funext fun i => Subsingleton.elim _ _)⟩
      infer_instance
    · refine ⟨fun x y => (hb n).1 (funext fun s => ((hD s).2.1 n ?_).elim _ _)⟩
      have : d s ≤ Finset.univ.sup d := Finset.le_sup (Finset.mem_univ s)
      omega
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PExtCont
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.extCont_of :
    ExtCont := by
  intro Γ F L _ _ _ _ _ _ _ hF M _ _ _ a ha v μ
  induction v using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add (f := _)]
    exact hx.add hy
  | tmul l m =>
    let b := Module.finBasis F M
    have key : ∀ g, μ ((LinearMap.baseChange L (a g)) (l ⊗ₜ m)) =
        ∑ i, algebraMap F L (b.coord i (a g m)) * μ (l ⊗ₜ b i) := by
      intro g
      rw [LinearMap.baseChange_tmul]
      conv_lhs => rw [← b.sum_repr (a g m)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.tmul_smul, ← algebraMap_smul L, map_smul, smul_eq_mul]
      rfl
    simp_rw [key]
    exact continuous_finsetSum _ fun i _ => (hF.comp (ha m (b.coord i))).mul continuous_const
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PFlagBasis
section
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem exists_linearIndep_levels_span_eq_of_monotone {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (W : ℕ → Submodule k V) (hW : Monotone W) (h0 : W 0 = ⊥) (n : ℕ) :
    ∃ (s : Set V) (lev : V → ℕ), LinearIndepOn k id s ∧ (∀ x ∈ s, lev x < n) ∧
      ∀ i ≤ n, Submodule.span k {x | x ∈ s ∧ lev x < i} = W i := by
  induction n with
  | zero =>
    refine ⟨∅, fun _ => 0, linearIndepOn_empty k id, by simp, ?_⟩
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    simp [h0]
  | succ n ih =>
    obtain ⟨s, lev, hs, hlev, hspan⟩ := ih
    have hsW : s ⊆ (W (n + 1) : Set V) := by
      intro x hx
      have hx' : x ∈ W n := by
        rw [← hspan n le_rfl]
        exact Submodule.subset_span ⟨hx, hlev x hx⟩
      exact hW (Nat.le_succ n) hx'
    obtain ⟨b, hbt, hsb, htb, hb⟩ := exists_linearIndepOn_id_extension hs hsW
    classical
    refine ⟨b, fun x => if x ∈ s then lev x else n, hb, ?_, ?_⟩
    · intro x hx
      by_cases h : x ∈ s
      · simp only [h, if_true]
        exact Nat.lt_succ_of_lt (hlev x h)
      · simp [h]
    · intro i hi
      rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
      · have hset : {x | x ∈ b ∧ (if x ∈ s then lev x else n) < i} = {x | x ∈ s ∧ lev x < i} := by
          ext x
          by_cases h : x ∈ s
          · simp [h, hsb h]
          · simp only [Set.mem_setOf_eq, h, if_false, false_and, iff_false]
            rintro ⟨-, h'⟩
            omega
        rw [hset]
        exact hspan i (Nat.lt_succ_iff.mp hi')
      · have hi2 : i = n + 1 := le_antisymm hi hi'
        subst hi2
        have hset : {x | x ∈ b ∧ (if x ∈ s then lev x else n) < n + 1} = b := by
          ext x
          constructor
          · exact fun h => h.1
          · intro hx
            refine ⟨hx, ?_⟩
            by_cases h : x ∈ s
            · simp only [h, if_true]
              exact Nat.lt_succ_of_lt (hlev x h)
            · simp [h]
        rw [hset]
        apply le_antisymm
        · exact Submodule.span_le.mpr hbt
        · intro y hy
          exact htb hy

theorem UpperTheory.Gal.Int.Geo.flagBasis_of :
    FlagBasis := by
  intro k _ d m W hW h0 hm
  obtain ⟨s, lev, hs, hlev, hspan⟩ := exists_linearIndep_levels_span_eq_of_monotone W hW h0 m
  have hall : ∀ i, Submodule.span k {x | x ∈ s ∧ lev x < i} = W i := by
    intro i
    rcases le_or_gt i m with h | h
    · exact hspan i h
    · have e1 : {x | x ∈ s ∧ lev x < i} = {x | x ∈ s ∧ lev x < m} := by
        ext x
        constructor
        · rintro ⟨hx, -⟩
          exact ⟨hx, hlev x hx⟩
        · rintro ⟨hx, h'⟩
          exact ⟨hx, by omega⟩
      have hle := hW h.le
      rw [hm] at hle
      rw [e1, hspan m le_rfl, hm]
      exact (top_le_iff.mp hle).symm
  have hsall : Submodule.span k s = ⊤ := by
    have e1 : {x | x ∈ s ∧ lev x < m} = s := by
      ext x
      exact ⟨fun h => h.1, fun h => ⟨h, hlev x h⟩⟩
    rw [← e1, hspan m le_rfl, hm]
  let b0 : Module.Basis s k (Fin d → k) :=
    Module.Basis.mk (v := ((↑) : s → Fin d → k)) hs (by rw [Subtype.range_coe]; exact hsall.ge)
  let e : s ≃ Fin d := b0.indexEquiv (Pi.basisFun k (Fin d))
  let b : Module.Basis (Fin d) k (Fin d → k) := b0.reindex e
  have hb : ∀ j, b j = (e.symm j : Fin d → k) := by
    intro j
    simp only [b, Module.Basis.reindex_apply]
    exact Module.Basis.mk_apply _ _ _
  let L := b.equivFun.symm
  let P : GL (Fin d) k :=
    ⟨LinearMap.toMatrix' (L : (Fin d → k) →ₗ[k] (Fin d → k)),
      LinearMap.toMatrix' (L.symm : (Fin d → k) →ₗ[k] (Fin d → k)),
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]⟩
  refine ⟨P, fun j => lev (e.symm j), ?_⟩
  intro i v
  have hPv : (↑P : Matrix (Fin d) (Fin d) k).mulVec v = L v := LinearMap.toMatrix'_mulVec _ v
  rw [hPv, ← hall i]
  have himg : (⇑b '' {j | lev (e.symm j) < i}) = {x | x ∈ s ∧ lev x < i} := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [hb]
      exact ⟨(e.symm j).2, hj⟩
    · rintro ⟨hx, hl⟩
      refine ⟨e ⟨x, hx⟩, ?_, ?_⟩
      · simpa using hl
      · rw [hb]
        simp
  rw [← himg, Module.Basis.mem_span_image]
  have hrep : ⇑(b.repr (L v)) = v := by
    rw [← Module.Basis.equivFun_apply]
    exact b.equivFun.apply_symm_apply v
  constructor
  · intro hv j hj
    change ∀ j, i ≤ lev (e.symm j) → v j = 0 at hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hrep] at hj
    show lev (e.symm j) < i
    by_contra hlt
    exact hj (hv j (not_lt.mp hlt))
  · intro hsub
    change ∀ j, i ≤ lev (e.symm j) → v j = 0
    intro j hj
    by_contra hne
    have hmem : j ∈ ((b.repr (L v)).support : Set (Fin d)) := by
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hrep]
      exact hne
    have h2 := hsub hmem
    simp only [Set.mem_setOf_eq] at h2
    omega
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PHopGal
section
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem comm_of_conj {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (A G G' : M →ₗ[R] M)
    (h : G ∘ₗ A ∘ₗ G' = A) (hid : G' ∘ₗ G = LinearMap.id) : A ∘ₗ G = G ∘ₗ A := by
  calc A ∘ₗ G = (G ∘ₗ A ∘ₗ G') ∘ₗ G := by rw [h]
    _ = G ∘ₗ A ∘ₗ (G' ∘ₗ G) := by simp only [LinearMap.comp_assoc]
    _ = G ∘ₗ A := by rw [hid, LinearMap.comp_id]

theorem UpperTheory.Gal.Int.Geo.hopGal_of :
    G3.HopSpec → OpConj → OpUniq → HopGal := by
  intro hS hC hU l _ k _ hl H Ω _ _ g d hd σ
  refine comm_of_conj _ _ (galTot l Ω H.q σ⁻¹)
    (hU l k hl H Ω g d hd _ (hC l k H Ω g _ σ (hS l hl H Ω g d hd).1)) ?_
  rw [← GlobalTheory.GalV.galTot_mul, inv_mul_cancel, GlobalTheory.GalV.galTot_one]
end

