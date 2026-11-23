module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMuSemidirectCyclicCoverOfMemGKinfCoeffs
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.KinfCover

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a]

theorem sigA_coeff_pt (g : GQ l) (w : Ainf l) (n : ℕ) : (Per.σA g w).coeff n = Per.σF g (w.coeff n) :=
  IsFractionRing.injective (OCb l) (Cb l)
    ((congrArg (WittVector.coeff · n) (galW_inclW g w)).symm.trans (autCb_alg l (galTilt l g) (w.coeff n)))

theorem exists_sigma_pow (g : GQ l) :
    ∃ m : ℕ, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ m) w) := by
  let ρ : Fq l a →+* Fq l a := ((Per.σF g).comp (Fq.val l a)).codRestrict (resSub l a) fun x => by
    rw [mem_resSub, RingHom.comp_apply, ← map_pow]
    exact congrArg (Per.σF g) (mem_resSub.1 x.2)
  have hρ : ∀ x, Fq.val l a (ρ x) = Per.σF g (Fq.val l a x) := fun _ => rfl
  letI : Algebra (ZMod l) (Fq l a) := ZMod.algebra _ l
  have := Fintype.ofFinite (Fq l a)
  let ψ : Fq l a →ₐ[ZMod l] Fq l a :=
    { ρ with commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (ρ.comp (algebraMap (ZMod l) (Fq l a))) (algebraMap (ZMod l) _)) r }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) (Fq l a)).2 ψ
  have hpow : ∀ x, ρ x = x ^ l ^ (j : ℕ) := fun x => by
    have h1 : ψ x = x ^ l ^ (j : ℕ) := by
      rw [← hj]
      simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
    exact h1
  refine ⟨j, fun w => WittVector.ext fun n => ?_⟩
  refine (sigA_coeff_pt g (wA l a w) n).trans ?_
  change Per.σF g (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ (j : ℕ)) w).coeff n)
  rw [coeff_sigma_pow, ← hpow, hρ]

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] (t : Wq l a →ₐ[ℤ_[l]] O)

theorem emb_sigma_pow (m : ℕ) (τ : ZMod a) (w : Wq l a) :
    emb t τ ((sigma l a ^ m) w) = emb t (τ - m) w := by
  induction m generalizing τ with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', AlgEquiv.mul_apply, emb_sigma, ih,
      show τ - 1 - (m : ZMod a) = τ - ((m + 1 : ℕ) : ZMod a) by push_cast; ring]

theorem galOA_constA_shift {g : GQ l} {m : ℕ}
    (hm : ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ m) w)) (x : ZMod a → O) :
    galOA O g (constA t x) = constA t fun τ => x (τ - m) := by
  obtain ⟨y, rfl⟩ := (splitHom_bijective t).2 x
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact (map_zero (constA t)).symm
  | tmul o w =>
    have : (fun τ => splitHom t (o ⊗ₜ w) (τ - m)) = splitHom t (o ⊗ₜ (sigma l a ^ m) w) :=
      funext fun τ => by rw [splitHom_tmul, splitHom_tmul, emb_sigma_pow]
    rw [this, constA_splitHom, constA_splitHom]
    exact (galOA_tmul g o _).trans (congrArg (fun y : Ainf l => o ⊗ₜ[ℤ_[l]] y) (hm w))
  | add y y' h h' =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), h, h', ← map_add (f := _)]
    rfl

theorem galOA_idem {g : GQ l} {m : ℕ}
    (hm : ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ m) w)) (τ : ZMod a) :
    galOA O g (idem (constA t) τ) = idem (constA t) (τ + m) := by
  rw [idem, galOA_constA_shift t hm, idem]
  congr 1
  ext1 σ
  simp only [Pi.single_apply, sub_eq_iff_eq_add]

variable {e : ℕ} [NeZero e] (ϖ : PiSys l e)

theorem kummer_pow {k : GQ l} (hk : k ∈ ϖ.GKinf) : ϖ.kummer k ^ e = 1 := by
  have hfix : ∀ n, k (ϖ.seq n ^ e) = ϖ.seq n ^ e := fun n =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk _ (IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩)
  refine Perfection.ext fun n => ?_
  have key : ∀ x : Perfection (ModP (OC l) l) l,
      Perfection.coeff (ModP (OC l) l) l n (x ^ e) = Perfection.coeff (ModP (OC l) l) l n x ^ e :=
    fun x => map_pow _ _ _
  refine (key (ϖ.kummer k)).trans (Eq.trans ?_ (map_one (Perfection.coeff (ModP (OC l) l) l n)).symm)
  change Ideal.Quotient.mk _ (ϖ.ratio k n) ^ e = 1
  rw [← map_pow, ← map_one (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}))]
  congr 1
  refine Subtype.ext ?_
  rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, hfix,
    div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)), map_one]
  rfl

theorem exists_kummer_eq (hsucc : e + 1 = l ^ a) {k : GQ l} (hk : k ∈ ϖ.GKinf) :
    ∃ z : Fq l a, Fq.val l a z = ϖ.kummer k ∧ z ^ e = 1 := by
  have h1 := kummer_pow ϖ hk
  have h2 : ϖ.kummer k ∈ resSub l a := by
    rw [mem_resSub, ← hsucc, pow_succ, h1, one_mul]
  exact ⟨(⟨_, h2⟩ : Fq l a), rfl, Fq.val_injective l a (((map_pow (Fq.val l a) _ e).trans h1).trans (map_one _).symm)⟩

variable [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]

omit [Fact l.Prime] in
theorem rescale_C_eq {R : Type} [CommRing R] (b r : R) : rescale b (C r) = C r := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

theorem galOA_evO {k : GQ l} (z : Fq l a) (hz : Fq.val l a z = ϖ.kummer k) (h : O⟦X⟧) :
    galOA O k (ϖ.evO O h) =
      glue (constA t) (ϖ.evO O) fun τ => rescale (emb t τ (WittVector.teichmuller l z)) h := by
  set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc
  have hu : constA t c = 1 ⊗ₜ wA l a (WittVector.teichmuller l z) := constA_emb t _
  have hk : galOA O k (ϖ.teichR O) = constA t c * ϖ.teichR O := by
    rw [ϖ.galOA_teichR O k, hu, PiSys.mu, tmul_sub, ← Algebra.TensorProduct.one_def, add_sub_cancel,
      wA_teich, hz]
  have hX' : ((galOA O k).toRingHom.comp (ϖ.evO O).toRingHom) X = constA t c * ϖ.teichR O := by
    change galOA O k (ϖ.evO O X) = _
    rw [PiSys.evO_X, hk]
  refine RingHom.congr_fun (ringHom_ext_of_sep ((galOA O k).toRingHom.comp (ϖ.evO O).toRingHom)
    ((glue (constA t) (ϖ.evO O)).toRingHom.comp (Pi.ringHom fun τ => rescale (c τ))) (fun r => ?_) ?_ ?_) h
  · change galOA O k (ϖ.evO O (C r)) = glue (constA t) (ϖ.evO O) (fun τ => rescale (c τ) (C r))
    simp only [rescale_C_eq]
    rw [glue_const]
    have h2 : ϖ.evO O (C r) = algebraMap O _ r := (ϖ.evO O).commutes r
    rw [h2, AlgHom.commutes]
  · rw [hX']
    change _ = glue (constA t) (ϖ.evO O) (fun τ => rescale (c τ) X)
    simp only [rescale_X]
    rw [glue_apply, eq_sum_idem (constA t) c, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, PiSys.evO_X, show ϖ.evO O (C (c τ)) = algebraMap O _ (c τ) from (ϖ.evO O).commutes _,
      mul_assoc]
  · intro x hx
    refine ϖ.sep_teichR O x fun n => ?_
    obtain ⟨y, hy⟩ := hx n
    exact ⟨constA t c ^ n * y, by rw [hy, hX', mul_pow]; ring⟩

variable (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]

theorem exists_covers {k : GQ l} (hk : k ∈ ϖ.GKinf) : ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  obtain ⟨m, hm⟩ := exists_sigma_pow (a := a) k
  obtain ⟨z, hz, hze⟩ := exists_kummer_eq (a := a) ϖ (TameDescentExponentData.succ_eq (K := K) (l := l) (e := e) (a := a)) hk
  let ζ : rootsOfUnity e K := rootsOfUnity.mkOfPowEq (algebraMap O K (t (WittVector.teichmuller l z))) (by
    rw [← map_pow, ← map_pow, ← map_pow, hze, map_one, map_one, map_one])
  refine ⟨⟨ζ, Multiplicative.ofAdd (m : ZMod a)⟩, fun f f' hf' => ?_⟩
  set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc
  have hroot : ∀ τ, TameGal.root (⟨ζ, Multiplicative.ofAdd (m : ZMod a)⟩ : TameGal K l e a) τ =
      algebraMap O K (c τ) := fun τ => by
    have h1 : c τ = t (WittVector.teichmuller l z) ^ l ^ (-τ).val := by
      change t ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) = _
      rw [sigma_pow_teich, map_pow]
    rw [h1, map_pow]
    change (((ζ ^ l ^ (-τ).val : rootsOfUnity e K) : Kˣ) : K) = _
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, rootsOfUnity.coe_mkOfPowEq]
  have hf'' : ∀ τ, f' τ = equivA O K (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := fun τ => by
    refine Subtype.ext ?_
    rw [hf' τ, ringAct_apply, hroot, coe_equivA, ← rescale_map, ← coe_equivA, AlgEquiv.apply_symm_apply]
    rfl
  have hRHS : ϖ.iTot t K f' =
      ∑ τ, idem (constA t) τ * ϖ.evO O (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := by
    rw [PiSys.iTot, glue_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hf'' τ, PiSys.iA_equivA]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hRHS, PiSys.iTot, glue_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.addRight (m : ZMod a)) _ _ fun σ => ?_
  rw [map_mul, galOA_idem t hm, Equiv.coe_addRight, add_sub_cancel_right]
  change _ * galOA O k (ϖ.evO O ((equivA O K).symm (f σ))) = _
  rw [galOA_evO t ϖ z hz, idem_mul_glue]

end GlobalTheory.KinfCover


open GlobalTheory.KinfCover in
theorem GlobalTheory.KinfCover.exists_covers_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), ∀ k ∈ ϖ.GKinf, ∃ γ : TameGal K l e a, Covers K t ϖ k γ :=
  fun _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ _ _ t ϖ _ hk => exists_covers t ϖ K hk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulEqTmulOfFrobeniusFixedFilZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrisFixedLattice

theorem coordLeft_lTensor {R : Type} [CommRing R] {V M N : Type}
    [AddCommGroup V] [Module R V] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {ι : Type} [DecidableEq ι] (b : Module.Basis ι R V) (f : M →ₗ[R] N) (x : V ⊗[R] M) (i : ι) :
    equivFinsuppOfBasisLeft b (f.lTensor V x) i = f (equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem coordRight_map {R : Type} [CommRing R] {M P N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    {κ : Type} [DecidableEq κ] (b : Module.Basis κ R N) (f : M →ₗ[R] P) (x : M ⊗[R] N) (j : κ) :
    equivFinsuppOfBasisRight b (TensorProduct.map f LinearMap.id x) j = f (equivFinsuppOfBasisRight b x j) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

variable {l : ℕ} [Fact l.Prime]

theorem padicInt_ringHom_ext_pt {R : Type} [CommRing R] [IsHausdorff (Ideal.span {(l : R)}) R]
    (f g : ℤ_[l] →+* R) (a : ℤ_[l]) : f a = g a := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {(l : R)}) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n a)
  have e : a = (a.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * c := by rw [← hc]; ring
  refine ⟨f c - g c, ?_⟩
  have hf := congrArg f e
  have hg := congrArg g e
  rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast] at hf hg
  rw [hf, hg]
  ring

theorem zA_eq_algebraMap_pt (a : ℤ_[l]) : Per.zA l a = algebraMap ℤ_[l] (Ainf l) a :=
  padicInt_ringHom_ext_pt (R := WittVector l (Per.Fl l)) (Per.zA l) _ a

theorem iota_algebraMap_pt (C : GlobalTheory.MemLoc.Core l) (a : ℤ_[l]) :
    C.ι (algebraMap ℤ_[l] (Per.Bcris l) a) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (Per.zA l a)) := by
  rw [zA_eq_algebraMap_pt]
  exact GlobalTheory.MemLoc.ULaws.iota_aB C _

def filZero (C : GlobalTheory.MemLoc.Core l) : Submodule ℤ_[l] (Per.Bcris l) where
  carrier := {b | C.ι b ∈ Per.FilD l 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact add_mem ha hb
  smul_mem' := by
    intro a b hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Algebra.smul_def, map_mul]
    have e : C.ι (algebraMap ℤ_[l] (Per.Bcris l) a) =
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (Per.zA l a)) := iota_algebraMap_pt C a
    rw [e, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hb

theorem qB_padicInt (C : GlobalTheory.MemLoc.Core l) (a : ℤ_[l]) :
    C.qB (a : ℚ_[l]) = algebraMap ℤ_[l] (Per.Bcris l) a := by
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [iota_algebraMap_pt, ← C.o_sec.z]
  exact C.ι_u _

theorem exists_padicInt_of_norm_le (q : ℚ_[l]) (N : ℕ) (h : ‖q‖ ≤ (l : ℝ) ^ N) :
    ‖(l : ℚ_[l]) ^ N * q‖ ≤ 1 := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
  rw [inv_mul_le_iff₀ (pow_pos hl N), mul_one]
  exact h

end GlobalTheory.CrisFixedLattice

namespace GlobalTheory.CrisFixedLattice

theorem frobOB_eq_lTensor {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (x : OB l O) : frobOB l O x = (frobB l).toLinearMap.lTensor O x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exists_pow_smul_eq_one_tmul : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (z : TW (OB l O) T), TWmap (frobOB l O) T z = z → z ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} → ∃ (n : ℕ) (x : ↥T.L.T), (l : O) ^ n • z = (1 : OB l O) ⊗ₜ[O] x := by
  intro hF l _ O K _ _ _ _ _ _ _ G _ _ T C z hφ hz
  classical
  rcases subsingleton_or_nontrivial O with hO | hO
  · haveI := Module.subsingleton O (TW (OB l O) T)
    exact ⟨0, 0, Subsingleton.elim _ _⟩
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  haveI : Module.Free O ↥T.L.T := T.L.free
  let bO := Module.Free.chooseBasis ℤ_[l] O
  let bM := Module.Free.chooseBasis O ↥T.L.T
  let eR := TensorProduct.equivFinsuppOfBasisRight (M := OB l O) bM
  let eL := TensorProduct.equivFinsuppOfBasisLeft (N := Per.Bcris l) bO
  let c := fun j i => eL (eR z j) i

  have hcφ : ∀ j i, Per.φB l (c j i) = c j i := by
    intro j i
    have h1 : eR (TWmap (frobOB l O) T z) j = frobOB l O (eR z j) :=
      coordRight_map bM (frobOB l O).toLinearMap z j
    rw [hφ, frobOB_eq_lTensor] at h1
    have h2 : c j i = eL ((frobB l).toLinearMap.lTensor O (eR z j)) i := congrArg (fun w => eL w i) h1
    rw [coordLeft_lTensor] at h2
    exact h2.symm

  let F0 := filZero C
  let RQ : Submodule ℤ_[l] (OB l O) := LinearMap.range (F0.subtype.lTensor O)
  have hsmul : ∀ (o : O) (w : OB l O), w ∈ RQ → o • w ∈ RQ := by
    rintro o _ ⟨y, rfl⟩
    refine ⟨(LinearMap.mulLeft ℤ_[l] o).rTensor _ y, ?_⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a f => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
  have key : ∀ w, w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} → ∀ j, eR w j ∈ RQ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w' hw' =>
      obtain ⟨β, x, hβ, rfl⟩ := hw'
      intro j
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
      refine hsmul _ _ ⟨(1 : O) ⊗ₜ[ℤ_[l]] (⟨β, hβ⟩ : F0), ?_⟩
      simp
    | zero => intro j; simp
    | add x y _ _ hx hy => intro j; rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx j) (hy j)
    | smul o x _ hx => intro j; rw [map_smul, Finsupp.smul_apply]; exact hsmul o _ (hx j)
  have hzR : ∀ j, eR z j ∈ RQ := key z hz
  have hcF : ∀ j i, C.ι (c j i) ∈ Per.FilD l 0 := by
    intro j i
    obtain ⟨y, hy⟩ := hzR j
    have h := coordLeft_lTensor bO F0.subtype y i
    simp only [c]
    rw [← hy, h]
    exact (equivFinsuppOfBasisLeft bO y i).2

  have hq : ∀ j i, ∃ q : ℚ_[l], C.qB q = c j i := fun j i => (hF l C).2.2.2.1 _ (hcφ j i) (hcF j i)
  choose q hqc using hq

  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ j, ∑ i, ‖q j i‖) hl1
  have hb : ∀ j i, ‖(l : ℚ_[l]) ^ N * q j i‖ ≤ 1 := fun j i => by
    refine exists_padicInt_of_norm_le _ N (le_trans ?_ hN.le)
    refine le_trans ?_ (Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun i _ => norm_nonneg (q j i))
      (Finset.mem_univ j))
    exact Finset.single_le_sum (fun i _ => norm_nonneg (q j i)) (Finset.mem_univ i)
  let a : _ → _ → ℤ_[l] := fun j i => ⟨(l : ℚ_[l]) ^ N * q j i, hb j i⟩
  have ha : ∀ j i, ((l ^ N : ℕ) : Per.Bcris l) * c j i = algebraMap ℤ_[l] (Per.Bcris l) (a j i) := by
    intro j i
    rw [← qB_padicInt, ← hqc]
    show _ = C.qB ((l : ℚ_[l]) ^ N * q j i)
    rw [map_mul, map_pow, map_natCast, Nat.cast_pow]
  let y : _ → O := fun j => bO.equivFun.symm (a j)
  refine ⟨N, bM.equivFun.symm y, ?_⟩
  apply eR.injective
  ext j : 1
  rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  apply eL.injective
  ext i : 1
  have e1 : bM.repr (bM.equivFun.symm y) j = y j := by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [e1, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul, Finsupp.smul_apply, map_nsmul, Finsupp.smul_apply,
    nsmul_eq_mul, ha, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  have e2 : bO.repr (y j) i = a j i := by
    simp only [y]
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [e2, Algebra.smul_def, mul_one]

end GlobalTheory.CrisFixedLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepMatrixCombinationKillingCharacters
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.MatCorner

variable {Γ A : Type} [Group Γ] [CommRing A] {r : ℕ}

def pairOf (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (g : Γ) :
    Matrix (Fin r) (Fin r) A × (ℕ → A) :=
  (mat ρ g, fun c => ((χ c g : Aˣ) : A))

theorem pairOf_mul (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (g h : Γ) :
    pairOf ρ χ (g * h) = pairOf ρ χ g * pairOf ρ χ h := by
  refine Prod.ext ?_ ?_
  · simp [pairOf, mat]
  · funext c
    simp [pairOf]

theorem mul_mem_span (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    {a b : Matrix (Fin r) (Fin r) A × (ℕ → A)}
    (ha : a ∈ Submodule.span A (Set.range (pairOf ρ χ)))
    (hb : b ∈ Submodule.span A (Set.range (pairOf ρ χ))) :
    a * b ∈ Submodule.span A (Set.range (pairOf ρ χ)) := by
  induction hb using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      rw [← pairOf_mul]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => simp
    | add x z _ _ hx hz =>
      rw [add_mul]
      exact Submodule.add_mem _ hx hz
    | smul c x _ hx =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c hx
  | zero => simp
  | add y z _ _ hy hz =>
    rw [mul_add]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hy

theorem exists_lift (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    (hs : Submodule.span A (Set.range (mat ρ)) = ⊤) (P : Matrix (Fin r) (Fin r) A) :
    ∃ v, (P, v) ∈ Submodule.span A (Set.range (pairOf ρ χ)) := by
  have hfst : (LinearMap.fst A (Matrix (Fin r) (Fin r) A) (ℕ → A)) ∘ pairOf ρ χ = mat ρ := by
    funext g
    rfl
  have hP : P ∈ (Submodule.span A (Set.range (pairOf ρ χ))).map
      (LinearMap.fst A (Matrix (Fin r) (Fin r) A) (ℕ → A)) := by
    rw [Submodule.map_span, ← Set.range_comp, hfst, hs]
    exact Submodule.mem_top
  obtain ⟨x, hx, rfl⟩ := hP
  exact ⟨x.2, by simpa using hx⟩

theorem pair_zero_mem (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (hr : 2 ≤ r)
    (hs : Submodule.span A (Set.range (mat ρ)) = ⊤) (P : Matrix (Fin r) (Fin r) A) :
    (P, (0 : ℕ → A)) ∈ Submodule.span A (Set.range (pairOf ρ χ)) := by
  set I := Submodule.span A (Set.range (pairOf ρ χ)) with hI

  have sand : ∀ M X Y : Matrix (Fin r) (Fin r) A, (M, (0 : ℕ → A)) ∈ I →
      (X * M * Y, (0 : ℕ → A)) ∈ I := by
    intro M X Y hM
    obtain ⟨v, hv⟩ := exists_lift ρ χ hs X
    obtain ⟨w, hw⟩ := exists_lift ρ χ hs Y
    have hXMY := mul_mem_span ρ χ (mul_mem_span ρ χ hv hM) hw
    simpa using hXMY
  obtain ⟨i0, i1, h01⟩ : ∃ i0 i1 : Fin r, i0 ≠ i1 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩

  have hE : (Matrix.single i0 i1 (1 : A), (0 : ℕ → A)) ∈ I := by
    obtain ⟨v, hv⟩ := exists_lift ρ χ hs (Matrix.single i0 i0 1)
    obtain ⟨w, hw⟩ := exists_lift ρ χ hs (Matrix.single i0 i1 1)
    have hc := I.sub_mem (mul_mem_span ρ χ hv hw) (mul_mem_span ρ χ hw hv)
    have hz : Matrix.single i0 i1 (1 : A) * Matrix.single i0 i0 1 = 0 :=
      Matrix.single_mul_single_of_ne (1 : A) i0 i1 i0 h01.symm 1
    simpa [hz, mul_comm w v] using hc

  have key : ∀ (i j : Fin r) (c : A), (Matrix.single i j c, (0 : ℕ → A)) ∈ I := by
    intro i j c
    have hij := sand _ (Matrix.single i i0 c) (Matrix.single i1 j 1) hE
    simpa using hij
  let J := I.comap (LinearMap.inl A (Matrix (Fin r) (Fin r) A) (ℕ → A))
  have hPJ : P ∈ J := by
    rw [Matrix.matrix_eq_sum_single P]
    exact J.sum_mem fun i _ => J.sum_mem fun j _ => key i j (P i j)
  exact hPJ

theorem exists_comb_kills_chars :
    ∀ {Γ A : Type} [Group Γ] [CommRing A] {r : ℕ} (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)), 2 ≤ r →
      Submodule.span A (Set.range (mat ρ)) = ⊤ → ∀ P : Matrix (Fin r) (Fin r) A,
      ∃ (m : ℕ) (f : Fin m → A) (h : Fin m → Γ), ∑ k, f k • mat ρ (h k) = P ∧
        ∀ c : ℕ, ∑ k, f k * ((χ c (h k) : Aˣ) : A) = 0 := by
  intro Γ A _ _ r ρ χ hr hs P
  obtain ⟨m, f, g, hg⟩ := Submodule.mem_span_set'.mp (pair_zero_mem ρ χ hr hs P)
  choose h hh using fun k => Set.mem_range.mp (g k).2
  have hsum : ∑ k, f k • pairOf ρ χ (h k) = (P, 0) := by simpa [hh] using hg
  refine ⟨m, f, h, ?_, fun c => ?_⟩
  · have h1 := congrArg Prod.fst hsum
    simpa [Prod.fst_sum, pairOf] using h1
  · have h2 := congrFun (congrArg Prod.snd hsum) c
    simpa [Prod.snd_sum, Finset.sum_apply, pairOf] using h2

end GlobalTheory.MatCorner
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaVanishingNoInvariantsFirstHalfPlacesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaVanishing_noInvariants_firstHalfPlaces : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → (∀ g, ∃ k : ℕ, κ g ^ (X.l i ^ k) = 1) → (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (b : Fin R), (∀ v, Over (P (.inl b)) v → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ Y g m = m) → m = 0) ∧ (AntiHom X.cc κ → (∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), κ τ = 1) → ∀ f : Z1 (repOn ρ κ Y), ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inl b))), f.1 τ = 0 ∧ f.1 (cConj X τ) = 0) := by
  first | exact @GlobalTheory.StageFirst.firstHalf | exact GlobalTheory.StageFirst.firstHalf | (intros; apply GlobalTheory.StageFirst.firstHalf <;> assumption)
end

