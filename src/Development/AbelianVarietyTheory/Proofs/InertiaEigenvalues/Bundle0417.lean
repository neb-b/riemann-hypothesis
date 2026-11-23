module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0365
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjOfTeichmullerCongr
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mem_OC_of_pow_eq {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : 0 < N) (a : ℂ_[l]) (c : OC l)
    (h : a ^ N = (c : ℂ_[l])) : a ∈ 𝓞_ℂ_[l] := by
  rw [GlobalTheory.RingBasics.mem_OC]
  have h1 := (GlobalTheory.RingBasics.mem_OC _).1 c.2
  rw [← h, norm_pow] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h1

theorem exists_OC_eq_of_pow_eq {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] [IsDomain D] (f : OC l →+* D)
    {N : ℕ} (hN : 0 < N) (c : OC l) (r : D) (h : r ^ N = f c) : ∃ s : OC l, f s = r := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (c : ℂ_[l]) hN
  haveI : NeZero (N : ℂ_[l]) := ⟨Nat.cast_ne_zero.2 hN.ne'⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[l] N
  let a' : OC l := ⟨a, mem_OC_of_pow_eq hN a c ha⟩
  let ζ' : OC l := ⟨ζ, mem_OC_of_pow_eq hN ζ 1 hζ.pow_eq_one⟩
  have hζ' : IsPrimitiveRoot ζ' N :=
    IsPrimitiveRoot.of_map_of_injective (f := (𝓞_ℂ_[l]).subtype) hζ Subtype.val_injective
  have ha' : a' ^ N = c := Subtype.ext ha
  have hp := congrArg (Polynomial.eval₂ f r) (X_pow_sub_C_eq_prod hζ' hN ha')
  rw [Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, h,
    sub_self, eq_comm, Finset.prod_eq_zero_iff] at hp
  obtain ⟨i, -, hi⟩ := hp
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at hi
  exact ⟨_, hi.symm⟩

theorem exists_alg_eq_of_pow_eq {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : 0 < N) (a : Om l) (s : ℂ_[l])
    (h : s ^ N = (a : ℂ_[l])) : ∃ z : Om l, s = (z : ℂ_[l]) := by
  have hf : (Polynomial.X ^ N - Polynomial.C a : Polynomial (Om l)) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero hN a
  have hroot : ((Polynomial.X ^ N - Polynomial.C a : Polynomial (Om l)).map
      (algebraMap (Om l) ℂ_[l])).IsRoot s := by
    simp only [Polynomial.IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [h]
    exact sub_self _
  obtain ⟨z, hz⟩ := (IsAlgClosed.splits _).mem_range_of_isRoot hf hroot
  exact ⟨z, hz.symm⟩

theorem eq_of_forall_dvd_root_sub {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [CharP O l] [PerfectRing O l]
    (c : O) [IsHausdorff (Ideal.span {c}) O] (v w : O)
    (h : ∀ n : ℕ, c ∣ ((frobeniusEquiv O l).symm)^[n] v - ((frobeniusEquiv O l).symm)^[n] w) : v = w := by
  have hp : ∀ (n : ℕ) (x : O), (((frobeniusEquiv O l).symm)^[n] x) ^ (l ^ n) = x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {c}) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h1 := pow_dvd_pow_of_dvd (h n) (l ^ n)
  rw [sub_pow_char_pow, hp, hp] at h1
  exact (pow_dvd_pow c (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le).trans h1

theorem exists_gal_of_teichmuller_congr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∀ v : O, WittVector.map ψ (bk.ev bk.E) ∣ WittVector.teichmuller l v - WittVector.teichmuller l (ψ bk.flat) → ∃ g : ↥(GK K), v = ψ (Per.σF (g : GQ l) bk.flat) := by
  intro l _ K bk O _ _ _ _ _ ψ h0 hu hc v hv
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨f, hf, hinj, hdom, hmod⟩ := _root_.GlobalTheory.BSP.exists_untilt_map l K bk O ψ h0 hu hc
  obtain ⟨hprime, hπ⟩ := _root_.GlobalTheory.BSP.BK.prime_unif l K bk
  obtain ⟨halg, hfix⟩ := _root_.GlobalTheory.BSP.rootT_flat_alg_and_fix l K bk
  set π : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ (X : bk.S)) with hπd
  have hft : ∀ y : OCb l, f y.untilt = Ideal.Quotient.mk _ (WittVector.teichmuller l (ψ y)) := fun y => by
    rw [← WittVector.fontaineTheta_teichmuller, ← WittVector.map_teichmuller]
    exact hf _
  let r : ℕ → WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)} := fun n =>
    Ideal.Quotient.mk _ (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] v))
  have hr0 : r 0 = f bk.flat.untilt := by
    rw [hft]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hv)
  have hrs : ∀ n, r (n + 1) ^ l = r n := fun n => by
    simp only [r]
    rw [← map_pow, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  have hrn : ∀ n, r n ^ (l ^ n) = f bk.flat.untilt := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_one, hr0]
    | succ n ih => rw [pow_succ', pow_mul, hrs, ih]
  choose s hs using fun n => exists_OC_eq_of_pow_eq f (pow_pos hl n) _ _ (hrn n)
  have hss : ∀ n, s (n + 1) ^ l = s n := fun n => hinj (by rw [map_pow, hs, hs, hrs])
  have hsn : ∀ n, s n ^ (l ^ n) = bk.flat.untilt := fun n => hinj (by rw [map_pow, hs, hrn])
  have hπc : ((bk.flat.untilt : OC l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l]) := by
    rw [← hπ, coe_intToOC]
  have hcoe : Function.Injective (fun z : Om l => (z : ℂ_[l])) := (algebraMap (Om l) ℂ_[l]).injective
  have hcp : ∀ (z : Om l) (m : ℕ), ((z ^ m : Om l) : ℂ_[l]) = (z : ℂ_[l]) ^ m :=
    fun z m => map_pow (algebraMap (Om l) ℂ_[l]) z m
  choose z hz using fun n => exists_alg_eq_of_pow_eq (pow_pos hl n) ((π : ↥K.1) : Om l) (s n : ℂ_[l])
    (by rw [← hπc, ← hsn n, SubmonoidClass.coe_pow])
  choose y hy using halg
  have hts : ∀ n, GlobalTheory.MemLoc.rootT bk.flat (n + 1) ^ l = GlobalTheory.MemLoc.rootT bk.flat n := fun n => by
    rw [GlobalTheory.MemLoc.rootT, GlobalTheory.MemLoc.rootT, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.galois_transitive_on_root_systems_of_prime l K π hprime y z
    (hcoe (by
      change ((y 0 : Om l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l])
      rw [← hy, ← hπc]
      rfl))
    (hcoe (by
      change ((z 0 : Om l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l])
      rw [← hz, ← hπc, ← hsn 0, pow_zero, pow_one]))
    (fun n => hcoe (by
      change ((y (n + 1) ^ l : Om l) : ℂ_[l]) = ((y n : Om l) : ℂ_[l])
      rw [hcp, ← hy, ← hy, ← hts n, SubmonoidClass.coe_pow]))
    (fun n => hcoe (by
      change ((z (n + 1) ^ l : Om l) : ℂ_[l]) = ((z n : Om l) : ℂ_[l])
      rw [hcp, ← hz, ← hz, ← hss n, SubmonoidClass.coe_pow]))
  obtain ⟨w, hw⟩ := GlobalTheory.tilt_of_compatible_roots l s hss
  have hgw : Per.σF (g : GQ l) bk.flat = w := hfix _ _ fun n => Subtype.ext (by
    refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (GlobalTheory.MemLoc.rootT bk.flat n)).trans ?_
    rw [hy, hw, hz, ← hg n]
    exact GlobalTheory.RingBasics.σC_coe _ _)
  refine ⟨g, ?_⟩
  rw [hgw]
  refine eq_of_forall_dvd_root_sub (l := l) (ψ bk.flat) v (ψ w) fun n => ?_
  have hψ : ∀ m, ψ (((frobeniusEquiv (OCb l) l).symm)^[m] w) = ((frobeniusEquiv O l).symm)^[m] (ψ w) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, RingHom.map_frobeniusEquiv_symm]
  have h1 := hft (((frobeniusEquiv (OCb l) l).symm)^[n] w)
  have h2 : f (s n) = Ideal.Quotient.mk _ (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] (ψ w))) := by
    rw [← hw n, ← hψ]
    exact h1
  have h3 := hmod (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] v) -
      WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] (ψ w)))
    (by rw [map_sub, ← h2, hs, sub_self]; exact dvd_zero _)
  rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
    WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at h3
  exact (dvd_pow_self _ bk.deg_pos.ne').trans h3

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisDeRhamLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.HodgeEx

theorem exists_hodge : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ N : ℕ, (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) → ∀ i, |(H.p i : ℤ) - H.q| ≤ N := by
  intro l _ K P AI T C hC ξ hξ d ρ hDR
  set M : ↥(GK K) → Matrix (Fin d) (Fin d) P.R.BdR :=
    fun g => (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) with hM
  have hKact : ∀ (g : ↥(GK K)) (k : ↥K.1) (v : P.R.BdR),
      P.actQdR (g : GQ l) (algebraMap ↥K.1 P.R.BdR k * v) = algebraMap ↥K.1 P.R.BdR k * P.actQdR (g : GQ l) v := by
    intro g k v
    rw [← P.PD_actdR, ← P.PD_actdR, map_mul, AlgEquiv.commutes]
  let Iv : Submodule ↥K.1 (Fin d → P.R.BdR) :=
    { carrier := {c | ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c}
      add_mem' := by
        intro u v hu hv g
        simp only [Set.mem_setOf_eq] at hu hv ⊢
        have : (fun i => P.actQdR (g : GQ l) ((u + v) i)) =
            (fun i => P.actQdR (g : GQ l) (u i)) + (fun i => P.actQdR (g : GQ l) (v i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add, hu g, hv g]
      zero_mem' := by
        intro g
        simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      smul_mem' := by
        intro k u hu g
        simp only [Set.mem_setOf_eq] at hu ⊢
        have : (fun i => P.actQdR (g : GQ l) ((k • u) i)) = k • (fun i => P.actQdR (g : GQ l) (u i)) := by
          funext i; simp only [Pi.smul_apply, Algebra.smul_def, hKact]
        rw [this, Matrix.mulVec_smul, hu g] }
  have hmemIv : ∀ c, c ∈ Iv ↔ ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c := fun c => Iff.rfl
  obtain ⟨x, hxli, hxinv, hxspan⟩ := _root_.GlobalTheory.DRMat.invariant_basis_of_isDR l P AI T K d ρ hDR
  set D : Submodule ↥K.1 (Fin d → P.R.BdR) := Submodule.span ↥K.1 (Set.range x) with hD
  have hDIv : D ≤ Iv := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (hmemIv _).2 (hxinv j))
  have hIvD : ∀ c, c ∈ Iv → c ∈ D := fun c hc => hxspan c hc
  haveI : FiniteDimensional ↥K.1 D := FiniteDimensional.span_of_finite ↥K.1 (Set.finite_range x)
  have hfr : Module.finrank ↥K.1 D = d := by
    rw [hD, finrank_span_eq_card hxli, Fintype.card_fin]
  let F : ℤ → Submodule ↥K.1 (Fin d → P.R.BdR) := fun a => Submodule.pi Set.univ (fun _ => (P.PD K).Fil a)
  have hmemF : ∀ a v, v ∈ F a ↔ ∀ i, v i ∈ (P.PD K).Fil a := fun a v => by
    simp [F, Submodule.mem_pi]
  have hFil : Antitone (P.PD K).Fil := antitone_int_of_succ_le (P.PD K).Fil_anti
  have hF : Antitone F := fun a b hab v hv => (hmemF _ _).2 fun i => hFil hab ((hmemF _ _).1 hv i)
  have hex : ∀ v ∈ D, ∃ a, v ∈ F a := by
    intro v _
    choose a ha using fun i => (P.PD K).Fil_exh (v i)
    refine ⟨-∑ i, |a i|, (hmemF _ _).2 fun i => hFil ?_ (ha i)⟩
    have h1 : |a i| ≤ ∑ j, |a j| := Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le (a i)
    linarith
  have hsep : ∀ v ∈ D, (∀ a, v ∈ F a) → v = 0 := fun v _ hv =>
    funext fun i => (P.PD K).Fil_sep (v i) fun a => (hmemF a v).1 (hv a) i
  set_option synthInstance.maxHeartbeats 200000 in
  obtain ⟨b0, h0, hbF0, hbrep0⟩ := GlobalTheory.T.exists_filtration_adapted_basis_of_subspace D F hF hex hsep
  set e := finCongr hfr
  set b := b0.reindex e with hb
  set h : Fin d → ℤ := fun j => h0 (e.symm j) with hh
  have hbF : ∀ j, (b j : Fin d → P.R.BdR) ∈ F (h j) ∧ (b j : Fin d → P.R.BdR) ∉ F (h j + 1) := fun j => by
    rw [hb, Module.Basis.reindex_apply]; exact hbF0 _
  have hbrep : ∀ (a : ℤ) (v : D), (v : Fin d → P.R.BdR) ∈ F a → ∀ j, b.repr v j ≠ 0 → a ≤ h j := by
    intro a v hv j hj
    rw [hb, Module.Basis.repr_reindex_apply] at hj
    exact hbrep0 a v hv _ hj
  have hbinv : ∀ j (g : ↥(GK K)), M g *ᵥ (fun i => P.actQdR (g : GQ l) ((b j : Fin d → P.R.BdR) i)) = (b j : Fin d → P.R.BdR) :=
    fun j => (hmemIv _).1 (hDIv (b j).2)
  have hspan : ∀ y : Fin d → P.R.BdR, (∀ i, y i ∈ (P.PD K).Fil 0) →
      ∃ c : Fin d → P.R.BdR, (∀ j, c j ∈ (P.PD K).Fil (-h j)) ∧ y = ∑ j, c j • (b j : Fin d → P.R.BdR) := by
    intro y hy
    obtain ⟨m, k, bb, z, hz, rfl⟩ := GlobalTheory.T.deRham_filtered_comparison_coordinates l P AI T K d ρ hDR 0 y hy
    have hzD : ∀ r, z r ∈ D := fun r => hIvD _ ((hmemIv _).2 (hz r).1)
    let cf : Fin m → Fin d → ↥K.1 := fun r j => b.repr ⟨z r, hzD r⟩ j
    refine ⟨fun j => ∑ r, cf r j • bb r, fun j => ?_, ?_⟩
    · refine Submodule.sum_mem _ fun r _ => ?_
      by_cases hc : cf r j = 0
      · rw [hc, zero_smul]; exact zero_mem _
      · have hkr := hbrep (k r) ⟨z r, hzD r⟩ ((hmemF _ _).2 (hz r).2.1) j hc
        refine Submodule.smul_mem _ _ (hFil ?_ (hz r).2.2)
        linarith
    · have hexp : ∀ r, z r = ∑ j, cf r j • (b j : Fin d → P.R.BdR) := fun r => by
        have := congrArg Subtype.val (b.sum_repr ⟨z r, hzD r⟩)
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this.symm
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      conv_lhs => enter [2, r]; rw [hexp r]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => ?_
      simp only [Algebra.smul_def]
      ring
  obtain ⟨H, hH⟩ := GlobalTheory.T.hodge_structure_of_adapted_invariant_family l K P AI T C hC ξ hξ d ρ (fun j => (b j : Fin d → P.R.BdR)) h hbinv
    (fun j i => (hmemF _ _).1 (hbF j).1 i) hspan
  refine ⟨H, fun N ⟨h1, h2⟩ i => ?_⟩
  rw [hH i]
  have hne : (b i : Fin d → P.R.BdR) ≠ 0 := fun h0' => b.ne_zero i (Subtype.ext h0')
  obtain ⟨hlo, hhi⟩ := GlobalTheory.T.deRham_filtration_bounds_invariant_coordinates l P K d ρ N h1 h2 _ (hbinv i) hne
  rw [abs_le]
  constructor
  · by_contra hlt
    push_neg at hlt
    exact (hbF i).2 (hF (show h i + 1 ≤ -(N : ℤ) by omega) ((hmemF _ _).2 hlo))
  · by_contra hlt
    push_neg at hlt
    exact hhi ((hmemF _ _).1 (hF (show (N : ℤ) + 1 ≤ h i by omega) (hbF i).1))

end GlobalTheory.HodgeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerCocycleTiltUniformizer
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.FlatKummer

theorem isPrimitiveRoot_of_seq {Ω : Type*} [Field Ω] (l : ℕ) [Fact l.Prime] (ζ : ℕ → Ω) (h0 : ζ 0 = 1)
    (hs : ∀ m, ζ (m + 1) ^ l = ζ m) (h1 : ζ 1 ≠ 1) (m : ℕ) : IsPrimitiveRoot (ζ m) (l ^ m) := by
  have hp : ∀ k, ζ k ^ l ^ k = 1 := by
    intro k
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [pow_succ', pow_mul, hs, ih]
  have h1' : ∀ k, ζ (k + 1) ^ l ^ k = ζ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, hs, ih]
  cases m with
  | zero => simp [h0]
  | succ m =>
    have h := orderOf_eq_prime_pow (x := ζ (m + 1)) (p := l) (n := m) (by rw [h1']; exact h1) (hp _)
    rw [← h]
    exact IsPrimitiveRoot.orderOf _

theorem exists_exponent_of_seq {Ω : Type*} [Field Ω] (l : ℕ) [Fact l.Prime] (ζ : ℕ → Ω) (h0 : ζ 0 = 1)
    (hs : ∀ m, ζ (m + 1) ^ l = ζ m) (h1 : ζ 1 ≠ 1) (z w : ℕ → Ω) (hz : ∀ m, z (m + 1) ^ l = z m)
    (hw : ∀ m, w (m + 1) ^ l = w m) (hwz : w 0 = z 0) :
    ∃ c : ℤ_[l], ∀ m, w m = ζ m ^ (PadicInt.toZModPow m c).val * z m := by
  have hne : ∀ m, NeZero (l ^ m) := fun m => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hiter : ∀ (x : ℕ → Ω), (∀ m, x (m + 1) ^ l = x m) → ∀ m, x m ^ l ^ m = x 0 := by
    intro x hx m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', pow_mul, hx, ih]
  by_cases hz0 : z 0 = 0
  · refine ⟨0, fun m => ?_⟩
    have a : z m = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 ((hiter z hz m).trans hz0)
    have b : w m = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1
      ((hiter w hw m).trans (hwz.trans hz0))
    rw [a, b, mul_zero]
  have hzm : ∀ m, z m ≠ 0 := fun m h => hz0 (by rw [← hiter z hz m, h, zero_pow (hne m).out])
  have hprim := isPrimitiveRoot_of_seq l ζ h0 hs h1
  have hpow : ∀ m a b : ℕ, ζ m ^ a = ζ m ^ b ↔ (a : ZMod (l ^ m)) = (b : ZMod (l ^ m)) := by
    intro m a b
    have hf : IsOfFinOrder (ζ m) := (hprim m).isOfFinOrder (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
    rw [hf.pow_eq_pow_iff_modEq, ← (hprim m).eq_orderOf, ZMod.natCast_eq_natCast_iff]
  have e1 : ∀ m, ∃ a : ℕ, w m = ζ m ^ a * z m := by
    intro m
    obtain ⟨a, -, ha⟩ := (hprim m).eq_pow_of_pow_eq_one (ξ := w m / z m) (by
      rw [div_pow, hiter w hw, hiter z hz, hwz, div_self hz0])
    exact ⟨a, by rw [ha, div_mul_cancel₀ _ (hzm m)]⟩
  choose a ha using e1
  have hd : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - (a i : ℤ) := by
    intro i
    have h2 := congrArg (· ^ l) (ha (i + 1))
    simp only [mul_pow, hw, hz] at h2
    rw [← pow_mul, mul_comm (a (i + 1)), pow_mul, hs, ha i] at h2
    have h3 := (hpow i _ _).mp (mul_right_cancel₀ (hzm i) h2)
    rw [ZMod.natCast_eq_natCast_iff] at h3
    exact_mod_cast h3.dvd
  refine ⟨PadicInt.ofIntSeq (fun i => (a i : ℤ)) (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ l hd),
    fun m => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ l hd, ha m]
  congr 1
  rw [hpow]
  simp

theorem rootT_succ_pow_l {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (m : ℕ) : rootT e (m + 1) ^ l = rootT e m := by
  rw [rootT, rootT, Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]

theorem exists_kummer_flat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l), ∃ c : ↥(GK K) → ℤ_[l],
    (∀ (g : ↥(GK K)) (m : ℕ), rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m (c g)).val * rootT bk.flat m) ∧ ∀ g, bk.FixFlat g → c g = 0 := by
  intro l _ K bk C
  obtain ⟨hz, -⟩ := GlobalTheory.BSP.rootT_flat_alg_and_fix l K bk
  choose z hz using hz
  have hinj : Function.Injective (algebraMap (Om l) ℂ_[l]) := (algebraMap (Om l) ℂ_[l]).injective
  have hz' : ∀ n, ((rootT bk.flat n : Per.OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (z n) := hz
  have hzs : ∀ m, z (m + 1) ^ l = z m := by
    intro m
    apply hinj
    rw [map_pow, ← hz', ← hz', ← rootT_succ_pow_l bk.flat m]
    push_cast
    rfl
  set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr
  have hθ : rootT bk.flat 0 = intToOC K r := by
    show bk.flat.untilt = _
    rw [← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]
    exact bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])
  have hz0 : z 0 = (((r : ↥K.1) : Om l)) := by
    apply hinj
    rw [← hz', hθ, coe_intToOC]
    rfl
  have good : ∀ g : ↥(GK K), ∃ c : ℤ_[l], ∀ m, rootT (Per.σF (g : GQ l) bk.flat) m =
      rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT bk.flat m := by
    intro g
    have hfix : (g : GQ l) (z 0) = z 0 := by
      rw [hz0]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2
    obtain ⟨c, hc⟩ := exists_exponent_of_seq l C.ζ C.ζ_zero C.ζ_succ C.ζ_one z (fun m => (g : GQ l) (z m)) hzs
      (fun m => by rw [← map_pow, hzs]) hfix
    refine ⟨c, fun m => ?_⟩
    have hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF (g : GQ l) bk.flat) =
        Per.σF (g : GQ l) (((frobeniusEquiv (Per.Fl l) l).symm)^[k] bk.flat) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
    have hsig : rootT (Per.σF (g : GQ l) bk.flat) m = Per.σO (g : GQ l) (rootT bk.flat m) := by
      rw [rootT, hit, GlobalTheory.RingBasics.untilt_σF]; rfl
    rw [hsig]
    apply Subtype.ext
    have h1 : ((Per.σO (g : GQ l) (rootT bk.flat m) : Per.OC l) : ℂ_[l]) = Per.σC (g : GQ l) (rootT bk.flat m : ℂ_[l]) :=
      by apply GlobalTheory.RingIface.sigO_coe
    have h2 : Per.σC (g : GQ l) (algebraMap (Om l) ℂ_[l] (z m)) = algebraMap (Om l) ℂ_[l] ((g : GQ l) (z m)) :=
      GlobalTheory.RingBasics.σC_coe (g : GQ l) _
    push_cast
    rw [h1, hz', h2, hc m, map_mul, map_pow, C.ε_root]
  classical
  refine ⟨fun g => if bk.FixFlat g then 0 else (good g).choose, fun g m => ?_, fun g hg => by simp [hg]⟩
  by_cases hg : bk.FixFlat g
  · simp only [hg, if_true, map_zero, ZMod.val_zero, pow_zero, one_mul]
    rw [show Per.σF (g : GQ l) bk.flat = bk.flat from hg]
  · simp only [hg, if_false]
    exact (good g).choose_spec m

end GlobalTheory.FlatKummer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemDecIsFrob
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem exists_mem_Dec_isFrob : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.E)) (A : ValuationSubring D.nd.Om), IsPlaceOver (F := D.host.E) A v → ∃ σ : Gen.GE D.nd, σ ∈ Dec (F := D.host.E) A ∧ IsFrob (F := D.host.E) A (normV v) σ := by
  intro D v A hA
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob (F := D.host.E) hA
  exact ⟨σ, hσ.1, hσ⟩

end GlobalTheory.TripleGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZeroProof
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exII_holds : ExII := _root_.GlobalTheory.PMonII.exII

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowInclRSmulMemStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_inclR_smul_mem' :
    ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ)
      {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (y : TW (RW LL) T),
      letI := twTop T b
      ∀ U ∈ 𝓝 (0 : TW (RW LL) T), ∃ k : ℕ, ∀ z : RA LL,
        inclR LL ((((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]]
          (WittVector.teichmuller l (AI.εroot s) - 1)) : RA LL) ^ k * z) • y ∈ U :=
  @GlobalTheory.WeakClosed.exists_pow_inclR_smul_mem
end

