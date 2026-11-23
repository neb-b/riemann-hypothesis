module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFamilyAdaptedToSeparatedFiltration
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem exists_family_adapted_filtration :
    ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W) (d : ℕ), Module.Finite E ↥D → Module.finrank E ↥D = d → (∀ a, F (a + 1) ≤ F a) → (∀ x, ∃ a, x ∈ F a) → (∀ x, (∀ a, x ∈ F a) → x = 0) → ∃ (x : Fin d → W) (u : Fin d → ℤ), (∀ k, x k ∈ D ∧ x k ∈ F (u k)) ∧ ∀ (a : ℤ) (c : Fin d → E), (∀ k, u k ≠ a → c k = 0) → ∑ k, c k • x k ∈ F (a + 1) → ∀ k, c k = 0 := by
  intro E W _ _ _ D F d hfin hd hF hex hsep
  have anti : Antitone F := antitone_int_of_succ_le hF
  induction d generalizing D with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun _ _ _ _ k => k.elim0⟩
  | succ d ih =>
    have hne : D ≠ ⊥ := by
      rintro rfl
      simp at hd
    have hinh : ∃ z, D ≤ F z := by
      obtain ⟨s, hs⟩ : D.FG := Module.Finite.iff_fg.mp hfin
      choose g hg using hex
      obtain ⟨m, hm⟩ := (s.image g).bddBelow
      refine ⟨m, ?_⟩
      rw [← hs, Submodule.span_le]
      intro y hy
      exact anti (hm (by simpa using ⟨y, hy, rfl⟩)) (hg y)
    have hbdd : ∃ b : ℤ, ∀ z, D ≤ F z → z ≤ b := by
      obtain ⟨y, hyD, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have : ∃ b, y ∉ F b := by
        by_contra h
        push Not at h
        exact hy0 (hsep y h)
      obtain ⟨b, hb⟩ := this
      refine ⟨b, fun z hz => ?_⟩
      by_contra h
      exact hb (anti (not_le.mp h).le (hz hyD))
    obtain ⟨lo, hlo, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
    have hnot : ¬ D ≤ F (lo + 1) := fun h => by have := hmax _ h; omega
    obtain ⟨x0, hx0D, hx0F⟩ := SetLike.not_le_iff_exists.mp hnot
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_notMem hx0F
    have hx0 : x0 ∉ D ⊓ LinearMap.ker f := fun h => hf0 h.2
    have hfin' : Module.Finite E ↥(D ⊓ LinearMap.ker f) :=
      Submodule.finiteDimensional_of_le (inf_le_left : D ⊓ LinearMap.ker f ≤ D)
    have hsup : (D ⊓ LinearMap.ker f) ⊔ Submodule.span E {x0} = D := by
      apply le_antisymm
      · exact sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hx0D)
      · intro y hy
        have h1 : y - (f y / f x0) • x0 ∈ D ⊓ LinearMap.ker f := by
          refine ⟨D.sub_mem hy (D.smul_mem _ hx0D), ?_⟩
          simp [LinearMap.mem_ker, div_mul_cancel₀ _ hf0]
        have h2 : (f y / f x0) • x0 ∈ Submodule.span E {x0} :=
          Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        simpa using Submodule.add_mem_sup h1 h2
    have hd' : Module.finrank E ↥(D ⊓ LinearMap.ker f) = d := by
      have hne0 : x0 ≠ 0 := fun h => hf0 (by simp [h])
      have := Submodule.finrank_sup_add_finrank_inf_eq (D ⊓ LinearMap.ker f) (Submodule.span E {x0})
      rw [hsup, hd, ((Submodule.disjoint_span_singleton' hne0).mpr hx0).eq_bot, finrank_bot,
        finrank_span_singleton hne0] at this
      omega
    obtain ⟨x, u, h1, h2⟩ := ih _ hfin' hd'
    refine ⟨Fin.cons x0 x, Fin.cons lo u, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · exact ⟨hx0D, hlo hx0D⟩
      · exact ⟨(h1 j).1.1, (h1 j).2⟩
    · intro a c hc hs
      rw [Fin.sum_univ_succ] at hs
      simp only [Fin.cons_zero, Fin.cons_succ] at hs
      have hc0 : c 0 = 0 := by
        by_cases ha : lo = a
        · subst ha
          have h3 := hf hs
          set_option synthInstance.maxHeartbeats 100000 in
            rw [LinearMap.mem_ker, map_add (f := _), map_sum, map_smul] at h3
          have h4 : ∑ j : Fin d, f (c j.succ • x j) = 0 :=
            Finset.sum_eq_zero fun j _ => by
              rw [map_smul, (LinearMap.mem_ker.mp (h1 j).1.2), smul_zero]
          rw [h4, add_zero, smul_eq_mul] at h3
          exact (mul_eq_zero.mp h3).resolve_right hf0
        · exact hc 0 ha
      rw [hc0, zero_smul, zero_add] at hs
      have h5 := h2 a (fun j => c j.succ) (fun j hj => hc j.succ hj) hs
      intro k
      exact Fin.cases hc0 h5 k

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FitsEx

theorem exists_lift {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (i : B →+* C)
    (hi : Function.Injective i) (f : A →+* C) (h : ∀ x, ∃ y, f x = i y) :
    ∃ g : A →+* B, ∀ x, i (g x) = f x := by
  choose g hg using h
  exact ⟨{ toFun := g
           map_one' := hi (by rw [← hg, map_one, map_one])
           map_mul' := fun x y => hi (by rw [map_mul, ← hg, ← hg, ← hg, map_mul])
           map_zero' := hi (by rw [← hg, map_zero, map_zero])
           map_add' := fun x y => hi (by rw [map_add (f := _), ← hg, ← hg, ← hg, map_add (f := _)]) }, fun x => (hg x).symm⟩

variable {l : ℕ} [Fact l.Prime]

theorem eps_root {P : LocPrime l} (AI : LocAinf l P) (m : ℕ) :
    (rootT (l := l) AI.ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (P.ζQ m) := by
  have : rootT (l := l) AI.ε m = AI.ζ m := by
    refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
    refine ⟨AI.ζ (m + n), ?_, by rw [zeta_pow_iter AI.ζ_succ]⟩
    have := zeta_coeff_root_iterate (p := l) (O := Per.OC l) AI.ε m n
    rw [add_comm] at this
    exact (AI.ε_coeff (m + n)).symm.trans this.symm
  rw [this]
  exact AI.ζ_eq m

theorem isLog_unique {e : Per.Fl l} (he : e.untilt = 1) {y y' : Per.BdRp l}
    (h : Per.IsLog l e y) (h' : Per.IsLog l e y') :
    y = y' :=
  GlobalTheory.CrisIncl.log_unique l e he y y' h h'

theorem exists_finExt (x : Om l) : ∃ K : FinExt l, x ∈ K.1 :=
  ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩,
    IntermediateField.mem_adjoin_simple_self _ x⟩

theorem iota_alg (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := by
  obtain ⟨K, hK⟩ := exists_finExt (c : Om l)
  rw [← P.PD_ι K]
  exact (P.PD K).ι.commutes (⟨c, hK, c.2⟩ : ↥(K0 K))

theorem iota_inj (P : LocPrime l) : Function.Injective P.ιB := by
  obtain ⟨K, -⟩ := exists_finExt (0 : Om l)
  intro a b h
  exact (P.PD K).ι_inj (by rw [P.PD_ι, P.PD_ι, h])

theorem phi_alg {P : LocPrime l} (AI : LocAinf l P) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.φB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (σ c) := by
  have key : P.φB.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B) =
      (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B).comp σ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[l] (S := MaximalUnramifiedExtension l) rfl fun x hx => ?_
    obtain ⟨m, hm, hlm, hxm⟩ := id hx
    obtain ⟨xb, hxb⟩ := exists_isTiltOf x m hm hlm hxm
    have hx' : x ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ hx
    have h1 := AI.ιA_teich ⟨x, hx'⟩ m hm hlm hxm xb hxb
    change P.φB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨x, hx'⟩) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (σ ⟨x, hx'⟩)
    rw [hσ ⟨x, hx'⟩ m hm hlm (Subtype.ext hxm), map_pow, ← h1, ← AI.ιA_φ, ← map_pow,
      WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  exact DFunLike.congr_fun key c

theorem sigma_eq {P : LocPrime l} (AI : LocAinf l P) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l)
    (K : FinExt l) (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)) (h : (c : Om l) = (x : Om l)) :
    (((P.PD K).σ x : ↥(K0 K)) : Om l) = ((σ c : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have : Nontrivial P.R.B := by
    refine ⟨⟨1, 0, fun h0 => one_ne_zero (AI.ιA_inj ?_)⟩⟩
    rw [map_one, map_zero, h0]
  have h1 := (P.PD K).φ_K₀ x
  rw [P.PD_φ] at h1
  have hc : c = ⟨x, x.2.2⟩ := Subtype.ext h
  have h2 := phi_alg AI σ hσ c
  rw [hc] at h2 ⊢
  have h3 : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨((P.PD K).σ x : ↥(K0 K)), ((P.PD K).σ x).2.2⟩ = _ := h1.symm.trans h2
  exact congrArg Subtype.val ((algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective h3)

theorem zeta_prim (P : LocPrime l) (m : ℕ) : IsPrimitiveRoot (P.ζQ (m + 1)) (l ^ (m + 1)) := by
  have h0 := zeta_pow_iter P.ζQ_succ 0 (m + 1)
  rw [zero_add, P.ζQ_zero] at h0
  have h1 := zeta_pow_iter P.ζQ_succ 1 m
  rw [add_comm] at h1
  have := orderOf_eq_prime_pow (x := P.ζQ (m + 1)) (p := l) (n := m) (by rw [h1]; exact P.ζQ_one) h0
  rw [← this]
  exact IsPrimitiveRoot.orderOf _

theorem chi_eq (P : LocPrime l) (χ : GQ l →* ℤ_[l]ˣ)
    (hχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val)
    (g : GQ l) : ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have key : ∀ m : ℕ, ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤
      (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by
    intro m
    have hp := zeta_prim P m
    obtain ⟨a, ha, hg⟩ := P.χQ_cyc g (m + 1) _ hp.pow_eq_one
    rw [hχ g (m + 1) _ hp.pow_eq_one] at hg
    have hmod : (PadicInt.toZModPow (m + 1) (χ g : ℤ_[l])).val ≡ a [MOD l ^ (m + 1)] := by
      have hfin : IsOfFinOrder (P.ζQ (m + 1)) :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos (Fact.out : l.Prime).pos _, hp.pow_eq_one⟩
      have := hfin.pow_eq_pow_iff_modEq.1 hg
      rwa [← hp.eq_orderOf] at this
    have hk : ((a : ℤ_[l]) - (χ g : ℤ_[l])) ∈ Ideal.span {(l : ℤ_[l]) ^ (m + 1)} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
        ← (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod]
      have : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      rw [ZMod.natCast_zmod_val, sub_self]
    have hn := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 hk
    have hn' : ‖(a : ℚ_[l]) - (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by
      simpa [PadicInt.norm_def] using hn
    rw [← sub_add_sub_cancel _ (a : ℚ_[l])]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hn')
  by_contra hne
  have hpos := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl)
  have h1 := key n
  rw [zpow_neg, zpow_natCast, ← inv_pow] at h1
  have h2 : (l : ℝ)⁻¹ ^ (n + 1) ≤ (l : ℝ)⁻¹ ^ n :=
    pow_le_pow_of_le_one (by positivity) (inv_lt_one_of_one_lt₀ hl).le (Nat.le_succ n)
  linarith

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem exists_fits : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ C : Core l, Fits T C := by
  intro l _ P AI T
  have hinj := (BdRField.bdR_isField l).2.1
  obtain ⟨o, ho⟩ := exists_lift _ hinj (T.eD.toRingHom.comp (algebraMap (Om l) P.R.BdR))
    fun x => (T.om x).imp fun _ h => h.1
  have hosec : IsSec o := by
    refine ⟨fun x => ?_, fun z => hinj ?_⟩
    · obtain ⟨y, hy, hy'⟩ := T.om x
      rw [← hy', hinj ((ho x).trans hy)]
    · rw [ho]
      change T.eD (algebraMap (Om l) P.R.BdR _) = _
      rw [← IsScalarTower.algebraMap_apply, T.zD]
      exact GlobalTheory.RingIface.zD_eq_alg l z
  have hincl := T.incl
  set ι := (T.eD.toRingHom.comp (P.ιB : P.R.B →+* P.R.BdR)).comp T.eB.symm.toRingHom with hι
  have hιe : ∀ b : P.R.B, T.eD (P.ιB b) = ι (T.eB b) := fun b => by simp [hι]
  clear_value ι
  obtain ⟨j, hj', hj0, hjb⟩ := GlobalTheory.CrisIncl.exists_restrict l ι hincl
  have hj : ∀ x, algebraMap (Per.BdRp l) (Per.BdR l) (j x) =
      (ι.comp (algebraMap (Per.Acris l) (Per.Bcris l))) x := fun x => (hj' x).symm
  have hjc : IsCrisP j := ⟨hj0, hjb⟩
  have he : PreTilt.untilt (AI.ε : Per.Fl l) = 1 := Subtype.ext (by
    have := eps_root AI 0
    rw [P.ζQ_zero, map_one] at this
    exact this)
  obtain ⟨t, -, ht, -⟩ := exists_isLogA l AI.ε he
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨χ, hχ⟩ := exists_cyclotomicChar l
  refine ⟨{ ζ := P.ζQ, ζ_zero := P.ζQ_zero, ζ_succ := P.ζQ_succ, ζ_one := P.ζQ_one
            ε := AI.ε, ε_root := eps_root AI, o := o, o_sec := hosec, j := j, j_cris := hjc
            ι := ι, ι_j := fun x => (hj x).symm
            u := T.eB.toRingHom.comp (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)
            ι_u := fun c => ?_
            t := t, t_log := ht, σ := σ, σ_root := hσ, χ := χ, χ_cyc := hχ },
    ⟨rfl, rfl, fun x => (ho x).symm, hιe, fun _ => rfl, ?_, chi_eq P χ hχ, sigma_eq AI σ hσ⟩⟩
  · rw [ho]
    exact (hιe _).symm.trans (congrArg T.eD (iota_alg P c))
  · obtain ⟨y, hy, hy'⟩ := T.t
    have h1 := isLog_unique he hy ((LogFun.log_fun l AI.ε t he ht).2.2.2 j hjc)
    have h2 : T.eD (P.ιB P.tB) = T.eD (P.ιB (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) t))) := by
      rw [hy', h1, hj, hιe, RingEquiv.apply_symm_apply]
      rfl
    rw [iota_inj P (T.eD.injective h2), RingEquiv.apply_symm_apply]
    rfl

end GlobalTheory.MemLoc.FitsEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGenerator
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.LineLattice

theorem exists_generator {LL : Type} [Field LL] {O : Type} [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] (T : Submodule O V) [Module.Free O T]
    (hsp : Submodule.span LL (T : Set V) = ⊤) (h1 : Module.finrank LL V = 1) :
    ∃ v : V, v ≠ 0 ∧ T = Submodule.span O {v} := by
  classical
  have hfin : Module.Finite LL V := Module.finite_of_finrank_eq_succ h1
  let b := Module.Free.chooseBasis O T
  have hli : LinearIndependent O (fun i => (b i : V)) :=
    b.linearIndependent.map' T.subtype T.ker_subtype
  have hli' : LinearIndependent LL (fun i => (b i : V)) :=
    (LinearIndependent.iff_fractionRing O LL).1 hli
  have hT : T = Submodule.span O (Set.range fun i => (b i : V)) := by
    have h := congrArg (Submodule.map T.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h.symm
  have hfi : Finite (Module.Free.ChooseBasisIndex O T) := hli'.finite
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex O T)
  have hc := hli'.fintype_card_le_finrank
  rw [h1] at hc
  have hsub : Subsingleton (Module.Free.ChooseBasisIndex O T) :=
    Fintype.card_le_one_iff_subsingleton.1 hc
  rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex O T) with he | ⟨⟨i⟩⟩
  · exfalso
    rw [Set.range_eq_empty, Submodule.span_empty] at hT
    have hb : Submodule.span LL (T : Set V) = ⊥ := by
      rw [hT]; simp
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h1
    exact bot_ne_top (hb.symm.trans hsp)
  · refine ⟨b i, hli.ne_zero i, ?_⟩
    refine hT.trans ?_
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      rw [Subsingleton.elim j i]; rfl
    · rintro rfl
      exact ⟨i, rfl⟩

theorem lattice_rank_one {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [IsDomain O] [Algebra O LL] [IsFractionRing O LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V} (L : Lattice (O := O) ρ)
    (h1 : Module.finrank LL V = 1) :
    (∃ e : LL ≃ₗ[LL] V, ∀ x : LL, e x ∈ L.T ↔ x ∈ Set.range (algebraMap O LL)) ∧
    ∀ a : O, a ≠ 0 →
      Nonempty (↥(Submodule.torsionBy O (V ⧸ L.T) a) ≃ₗ[O] (O ⧸ Ideal.span {a})) := by
  haveI := L.free
  obtain ⟨v, hv, hT⟩ := exists_generator L.T L.span h1
  have hsurj : ∀ w : V, ∃ c : LL, c • v = w := (finrank_eq_one_iff_of_nonzero' v hv).1 h1
  have hmem : ∀ x : LL, x • v ∈ L.T ↔ x ∈ Set.range (algebraMap O LL) := by
    intro x
    rw [hT, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [← algebraMap_smul LL c v] at hc
      exact smul_left_injective LL hv hc
    · rintro ⟨c, rfl⟩
      exact ⟨c, (algebraMap_smul LL c v).symm⟩
  refine ⟨⟨LinearEquiv.ofBijective (LinearMap.toSpanSingleton LL V v)
    ⟨smul_left_injective LL hv, hsurj⟩, hmem⟩, ?_⟩
  intro a ha
  have ha' : algebraMap O LL a ≠ 0 := by
    simpa using ha
  have hx : L.T.mkQ ((algebraMap O LL a)⁻¹ • v) ∈ Submodule.torsionBy O (V ⧸ L.T) a := by
    rw [Submodule.mem_torsionBy_iff, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL a, smul_smul, hmem,
      mul_inv_cancel₀ ha']
    exact ⟨1, map_one _⟩
  let f : O →ₗ[O] Submodule.torsionBy O (V ⧸ L.T) a :=
    LinearMap.toSpanSingleton O _ ⟨_, hx⟩
  have hf : ∀ c : O, (f c : V ⧸ L.T) =
      L.T.mkQ ((algebraMap O LL c * (algebraMap O LL a)⁻¹) • v) := by
    intro c
    rw [← smul_smul, algebraMap_smul, map_smul]
    rfl
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := L.T.mkQ_surjective y
    obtain ⟨x, rfl⟩ := hsurj w
    rw [Submodule.mem_torsionBy_iff, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, ← algebraMap_smul LL a, smul_smul, hmem] at hy
    obtain ⟨c, hc⟩ := hy
    refine ⟨c, Subtype.ext ?_⟩
    rw [hf, hc, mul_comm (algebraMap O LL a) x, mul_assoc, mul_inv_cancel₀ ha', mul_one]
  have hk : LinearMap.ker f = Ideal.span {a} := by
    ext c
    rw [LinearMap.mem_ker, Subtype.ext_iff, hf, Ideal.mem_span_singleton']
    rw [Submodule.coe_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmem]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, IsFractionRing.injective O LL ?_⟩
      rw [map_mul, hd, mul_assoc, inv_mul_cancel₀ ha', mul_one]
    · rintro ⟨d, rfl⟩
      refine ⟨d, ?_⟩
      rw [map_mul, mul_assoc, mul_inv_cancel₀ ha', mul_one]
  exact ⟨(f.quotKerEquivOfSurjective hfs).symm.trans (Submodule.quotEquivOfEq _ _ hk)⟩

end GlobalTheory.LineLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemGKChiPowNeOne
section
namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

private lemma norm_one_add_prime_padic (l : ℕ) [Fact l.Prime] : ‖(1 : ℚ_[l]) + l‖ = 1 := by
  have h1 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hne : ‖(1 : ℚ_[l])‖ ≠ ‖(l : ℚ_[l])‖ := by rw [norm_one]; exact ne_of_gt h1
  first
  | rw [padicNormE.add_eq_max_of_ne hne, norm_one]; exact max_eq_left h1.le
  | rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]; exact max_eq_left h1.le

private lemma zmod_pow_ne_one_of_pow_mod_ne_one (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 0 < n) :
    ((1 : ℚ_[l]) + l) ^ n ≠ 1 := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have key : (1 + l) ^ n ≠ 1 := (Nat.one_lt_pow (by omega) (by omega)).ne'
  intro h
  apply key
  exact_mod_cast h

theorem exists_mem_GK_chi_pow_ne_one : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ →
    ∀ (K : FinExt l) (e : ℕ), 0 < e → ∃ g ∈ GK K, (χ g : ℚ_[l]) ^ e ≠ 1 := by
  intro l _ χ hχ K e he

  obtain ⟨σ, -, hσ⟩ := exists_chi_eq K χ hχ _ (norm_one_add_prime_padic l)
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2

  let f : ℕ → (↥K.1 →ₐ[ℚ_[l]] Om l) := fun n =>
    (AlgEquiv.toAlgHom (σ ^ n : Om l ≃ₐ[ℚ_[l]] Om l)).comp (IntermediateField.val K.1)
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f

  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ g ∈ GK K, (χ g : ℚ_[l]) ^ e ≠ 1 := by
    intro a b hab hfab
    refine ⟨σ ^ (b - a), ?_, ?_⟩
    · unfold GK
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : (σ ^ a) x = (σ ^ b) x :=
        congrArg (fun φ : ↥K.1 →ₐ[ℚ_[l]] Om l => φ ⟨x, hx⟩) hfab
      have hb : σ ^ b = σ ^ a * σ ^ (b - a) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hb, AlgEquiv.mul_apply] at h1
      exact ((σ ^ a).injective h1).symm
    · rw [map_pow, Units.val_pow_eq_pow_val, hσ, ← pow_mul]
      exact zmod_pow_ne_one_of_pow_mod_ne_one l _ (Nat.mul_pos (by omega) he)
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hfij
  · exact key j i h hfij.symm

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCharacterOfGaloisStableLineCLTate
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_unit_character_of_stable_line (l : ℕ) [Fact l.Prime] (y : ℂ_[l]) (hy : y ≠ 0)
    (h : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σC g y = algebraMap ℚ_[l] ℂ_[l] x * y) :
    ∃ η : GQ l →* ℤ_[l]ˣ, ∀ g : GQ l,
      Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y := by
  choose x hx using h
  have hn : ∀ g, ‖x g‖ = 1 := fun g => by
    have h1 := GlobalTheory.RingBasics.norm_σC g y
    rw [hx, norm_mul, norm_algebraMap'] at h1
    exact mul_right_cancel₀ (norm_ne_zero_iff.2 hy) (h1.trans (one_mul _).symm)
  have hm : ∀ g k, x (g * k) = x g * x k := fun g k => by
    apply (algebraMap ℚ_[l] ℂ_[l]).injective
    apply mul_right_cancel₀ hy
    rw [← hx, GlobalTheory.RingBasics.σC_mul, hx k, map_mul, TateTwist.σC_algebraMap, hx g, map_mul]
    ring
  refine ⟨MonoidHom.mk' (fun g => PadicInt.mkUnits (hn g)) fun g k => ?_, fun g => hx g⟩
  apply Units.ext
  apply Subtype.ext
  exact hm g k

end GlobalTheory.Per
end

