module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0358
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InModIffForallPlaceMemSpanModulo
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.GroupLoc.Crt

theorem mem_sup_prod_smul {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] (T N : Submodule R M)
    (I : ι → Ideal R) (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) {y : M} (hy : y ∈ N) (s : Finset ι)
    (h : ∀ i ∈ s, y ∈ T ⊔ I i • N) : y ∈ T ⊔ (∏ i ∈ s, I i) • N := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Submodule.mem_sup_right hy
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have h1 := h i (Finset.mem_insert_self _ _)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hc : IsCoprime (I i) (∏ j ∈ s, I j) :=
      IsCoprime.prod_right fun j hj => hI i j (fun e => hi (e ▸ hj))
    obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hc
    have key : ∀ (A B : Ideal R) (c : R), c ∈ A → y ∈ T ⊔ B • N → c • y ∈ T ⊔ (A * B) • N := by
      intro A B c hc hy
      obtain ⟨t, ht, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
      rw [smul_add]
      refine Submodule.add_mem_sup (T.smul_mem c ht) ?_
      rw [Submodule.mul_smul]
      exact Submodule.smul_mem_smul hc hz
    have e : y = a • y + b • y := by rw [← add_smul, hab, one_smul]
    rw [e]
    refine Submodule.add_mem _ (key _ _ a ha h2) ?_
    rw [mul_comm]
    exact key _ _ b hb h1

theorem mem_sup_smul_mono {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {T N : Submodule R M}
    {I J : Ideal R} (h : I ≤ J) {y : M} (hy : y ∈ T ⊔ I • N) : y ∈ T ⊔ J • N :=
  (sup_le_sup_left (Submodule.smul_mono_left h) T : T ⊔ I • N ≤ T ⊔ J • N) hy

theorem prod_le_span {O : Type*} [CommRing O] [IsDedekindDomain O] {g : O} (hg : g ≠ 0)
    (hsq : ∀ w : HeightOneSpectrum O, g ∉ w.asIdeal ^ 2) (s : Finset (HeightOneSpectrum O))
    (hs : ∀ w : HeightOneSpectrum O, g ∈ w.asIdeal → w ∈ s) :
    ∏ w ∈ s, w.asIdeal ≤ Ideal.span {g} := by
  have h0 : (Ideal.span {g} : Ideal O) ≠ ⊥ := fun e => hg (Ideal.span_singleton_eq_bot.1 e)
  have hsf : Squarefree (Ideal.span {g} : Ideal O) := by
    refine (squarefree_iff_no_irreducibles (x := (Ideal.span {g} : Ideal O)) h0).2 ?_
    intro x hx hd
    have hp : Prime x := UniqueFactorizationMonoid.irreducible_iff_prime.1 hx
    refine hsq ⟨x, Ideal.isPrime_of_prime hp, hp.ne_zero⟩ ?_
    rw [Ideal.dvd_span_singleton, ← pow_two] at hd
    exact hd
  have hrad : (Ideal.span {g}).radical ≤ Ideal.span {g} := by
    rintro x ⟨n, hn⟩
    rw [← Ideal.dvd_span_singleton] at hn ⊢
    rw [← Ideal.span_singleton_pow] at hn
    exact hsf.isRadical n _ hn
  refine le_trans ?_ hrad
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro P ⟨hP1, hP2⟩
  have hP0 : P ≠ ⊥ := fun e => h0 (le_bot_iff.1 (hP1.trans e.le))
  have hm := hs ⟨P, hP2, hP0⟩ ((Ideal.span_singleton_le_iff_mem _).1 hP1)
  have hle : ∏ w ∈ s, w.asIdeal ≤ (⟨P, hP2, hP0⟩ : HeightOneSpectrum O).asIdeal :=
    (Ideal.prod_le_inf (s := s) (f := fun w : HeightOneSpectrum O => w.asIdeal)).trans (Finset.inf_le hm)
  exact hle

variable {D : D7}

theorem g_not_mem_sq (w : HeightOneSpectrum (𝓞 D.host.E)) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 := by
  intro hm
  have hc : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
  have key : ∀ k (b : 𝓞 D.host.E), IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) b →
      ((D.host.g k : ℕ) : 𝓞 D.host.E) * b ∈ w.asIdeal ^ 2 → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    rintro k b ⟨u, v, huv⟩ h hk
    refine (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hk).2.1 ?_
    have e : ((D.host.g k : ℕ) : 𝓞 D.host.E) =
        u * ((D.host.g k : ℕ) : 𝓞 D.host.E) ^ 2 + v * (((D.host.g k : ℕ) : 𝓞 D.host.E) * b) := by
      linear_combination (-((D.host.g k : ℕ) : 𝓞 D.host.E)) * huv
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hk 2)) (Ideal.mul_mem_left _ _ h)
  rw [Nat.cast_mul] at hm
  rcases w.isPrime.mem_or_mem (Ideal.pow_le_self two_ne_zero hm) with h | h
  · exact key 0 _ hc hm h
  · exact key 1 _ hc.symm (mul_comm (G := 𝓞 D.host.E) _ _ ▸ hm) h

def toInt (I : Formalism.MainNotions.S.AutInst) : 𝓞 I.E →+* Formalism.MainNotions.S.IntAf I.F I.E :=
  ((Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)).comp (algebraMap (𝓞 I.E) I.E)).codRestrict _ fun t =>
    Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 I.E) I.E t, ⟨t, rfl⟩⟩, rfl⟩)

theorem toInt_smul (I : Formalism.MainNotions.S.AutInst) (a : 𝓞 I.E) (y : Fin I.n → I.E) :
    toInt I a • incl I y = incl I ((a : I.E) • y) := by
  funext i
  show Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (a : I.E) * Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (y i) =
    Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((a : I.E) * y i)
  rw [map_mul]

def hostInt (X : HidaSetting D) : 𝓞 D.host.E →+* Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
  (toInt X.B.I).comp (RingOfIntegers.mapRingEquiv X.ιE.symm).toRingHom

theorem wLf_eq (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    wLf X w = (w.asIdeal.map (hostInt X)) • X.B.I.Lf := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    show incl X.B.I x ∈ (w.asIdeal.map (hostInt X)) • X.B.I.Lf
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ⟨b, hb, hab⟩, y, hy, rfl⟩ := hz
      rw [← toInt_smul]
      have : toInt X.B.I a = hostInt X b := by
        refine congrArg (toInt X.B.I) (RingOfIntegers.ext ?_)
        show (a : X.B.I.E) = X.ιE.symm (b : D.host.E)
        rw [← hab, RingEquiv.symm_apply_apply]
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hb) (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)
    | zero =>
      have : incl X.B.I 0 = 0 := funext fun i => map_zero _
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : incl X.B.I (x + y) = incl X.B.I x + incl X.B.I y := funext fun i => map_add _ _ _
      rw [this]; exact add_mem hx hy
    | smul a x _ hx =>
      have : incl X.B.I (a • x) = toInt X.B.I a • incl X.B.I x := (toInt_smul _ a x).symm
      rw [this]; exact Submodule.smul_mem _ _ hx
  · unfold Ideal.map
    rw [show X.B.I.Lf = Submodule.span _ (Set.range fun x : X.B.I.L => incl X.B.I x) from rfl]
    rw [Submodule.span_smul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨b, hb, rfl⟩, _, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
    show toInt X.B.I (RingOfIntegers.mapRingEquiv X.ιE.symm b) • incl X.B.I y ∈ wLf X w
    rw [toInt_smul]
    refine Submodule.subset_span ⟨⟨_, Submodule.subset_span ⟨_, ⟨b, hb, ?_⟩, y, hy, rfl⟩⟩, rfl⟩
    exact X.ιE.apply_symm_apply _

theorem mL_eq (X : HidaSetting D) (m : ℕ) :
    mL X.B.I m = ((Ideal.span {(m : 𝓞 D.host.E)}).map (hostInt X)) • X.B.I.Lf := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.smul_mem_smul (r := (m : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)) (Ideal.mem_span_singleton_self _) hx
  · refine Submodule.smul_le.2 fun r hr x hx => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)

theorem inMod_iff_forall_modW : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (S : Set (VA X.B.I)), S ⊆ X.B.I.Lf → ∀ y ∈ X.B.I.Lf, (InMod X.B.I X.B.g S y ↔ ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.GroupLoc.ModW X w S y) := by
  intro D X _ _ S _ y hy
  unfold InMod ModW
  simp only [mL_eq, wLf_eq]
  constructor
  · intro h w hw
    exact mem_sup_smul_mono (Ideal.map_mono ((Ideal.span_singleton_le_iff_mem _).2 hw)) h
  · intro h
    have hg : ((X.B.g : ℕ) : 𝓞 D.host.E) ≠ 0 := by
      rw [X.g_eq]
      exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
    have hfin : {w : HeightOneSpectrum (𝓞 D.host.E) | ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal}.Finite := by
      have := Ideal.finite_factors (I := Ideal.span {((X.B.g : ℕ) : 𝓞 D.host.E)}) (by simpa using hg)
      simpa only [Ideal.dvd_span_singleton] using this
    have h1 := mem_sup_prod_smul _ _ (fun w : HeightOneSpectrum (𝓞 D.host.E) => w.asIdeal.map (hostInt X))
      (fun i j hij => by
        rw [Ideal.isCoprime_iff_sup_eq, ← Ideal.map_sup,
          i.isMaximal.coprime_of_ne j.isMaximal (fun e => hij (HeightOneSpectrum.ext e)), Ideal.map_top])
      hy hfin.toFinset (fun w hw => h w (hfin.mem_toFinset.1 hw))
    refine mem_sup_smul_mono ?_ h1
    have h2 := prod_le_span hg (fun w => by rw [X.g_eq]; exact g_not_mem_sq w) hfin.toFinset
      (fun w hw => hfin.mem_toFinset.2 hw)
    refine le_trans (le_of_eq ?_) (Ideal.map_mono h2)
    exact (map_prod (Ideal.mapHom (hostInt X)) _ _).symm

end GlobalTheory.Mem.GroupLoc.Crt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMatrixModPlaceInFamilyInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymFrame

theorem invMat_quot {Q ι : Type} [AddCommGroup Q] [Fintype ι] [DecidableEq ι] {g : ℕ} [NeZero g] [Fact (1 < g)]
    (T S : Q →+ Q) (hST : ∀ q, S (T q) = q) (β : ι → Q) (hβ : ∀ i, g • β i = 0)
    (N N' : Matrix ι ι (ZMod g)) (hNN' : N * N' = 1)
    (hT : ∀ i, T (β i) = ∑ j, (N j i).val • β j) (m : ι) :
    S (β m) = ∑ i, (N' i m).val • β i := by
  have e1 : T (∑ i, (N' i m).val • β i) = ∑ l, ((N * N') l m).val • β l := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_nsmul, hT, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, val_mul_nsmul _ (hβ l)]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have e2 : ∑ l, (((1 : Matrix ι ι (ZMod g))) l m).val • β l = β m := by
    rw [Finset.sum_eq_single m]
    · rw [Matrix.one_apply_eq, ZMod.val_one, one_smul]
    · intro l _ hl
      rw [Matrix.one_apply_ne hl, ZMod.val_zero, zero_smul]
    · intro h; exact absurd (Finset.mem_univ m) h
  rw [hNN', e2] at e1
  rw [← e1, hST]

end GlobalTheory.Mem.SymFrame

namespace GlobalTheory.Mem.SymFrame

theorem isMatIn_inv : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (u : Fin D.R.r → VA X.B.I), (∀ i, u i ∈ X.B.I.Lf) → ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k⁻¹ ((N⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  intro D X kv hg u hu k hk N hN m
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  haveI : Fact (1 < D.host.g kv.1) := ⟨(D.host.g_prime kv.1).one_lt⟩
  let W := (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup
  have hk' : k⁻¹ ∈ X.B.I.Kset := Formalism.L2.SG.Pf.unitaryCongruence.K_inv X.B.I hk
  let fT := (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom
  let fS := (Matrix.mulVecLin (X.B.I.fmat k⁻¹)).toAddMonoidHom
  let T := QuotientAddGroup.map W W fT (fun v hv => fmat_mulVec_mem_wLf X _ hk hv)
  let S := QuotientAddGroup.map W W fS (fun v hv => fmat_mulVec_mem_wLf X _ hk' hv)
  have key : ∀ a b : VA X.B.I, a - b ∈ wLf X (D.naut.plGw kv.1 kv.2) ↔ QuotientAddGroup.mk' W a = QuotientAddGroup.mk' W b := fun a b => by
    show a - b ∈ W ↔ _
    rw [← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  have hST : ∀ q, S (T q) = q := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H v =>
      show QuotientAddGroup.mk' W (X.B.I.fmat k⁻¹ *ᵥ (X.B.I.fmat k *ᵥ v)) = QuotientAddGroup.mk' W v
      rw [Matrix.mulVec_mulVec, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul X.B.I k, Matrix.one_mulVec]
  have hβ : ∀ i, D.host.g kv.1 • QuotientAddGroup.mk' W (u i) = 0 := fun i => by
    rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    have h1 := inclE_smul_mem_wLf X (D.naut.plGw kv.1 kv.2) ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E)
      ⟨_, hg, by simp⟩ (y := u i) (hu i)
    have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) : X.B.I.E) =
        ((D.host.g kv.1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
      simp [map_natCast]
    rw [e, Nat.cast_smul_eq_nsmul] at h1
    exact h1
  have hT : ∀ i, T (QuotientAddGroup.mk' W (u i)) =
      ∑ j, ((N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • QuotientAddGroup.mk' W (u j) := by
    intro i
    have := (key _ _).1 (by simpa only [Nat.cast_smul_eq_nsmul] using hN i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_nsmul] at this
    rw [← this]; rfl
  have h := invMat_quot T S hST (fun i => QuotientAddGroup.mk' W (u i)) hβ
    (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))
    ((N⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hT m
  simp only [Nat.cast_smul_eq_nsmul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_sum]
  simp only [map_nsmul]
  rw [← h]; rfl

end GlobalTheory.Mem.SymFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFrameCharacterMulMovedPointStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFrameCharacter_mul_movedPoint : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (χ : U →* ℂˣ) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ → χ x = Units.map (σ : K →* ℂ) (Λ.chr h)) → ∀ (x : topU U t Θ d) (h : Λ.grp) (θ : Θ.grp), IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x.1 * (k * t)) (((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) → χ ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Λ.chr h * Θ.chr θ) := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.chi_mul_topChi_moved | exact GlobalTheory.Mem.Col2.TopCh.chi_mul_topChi_moved | (intros; apply GlobalTheory.Mem.Col2.TopCh.chi_mul_topChi_moved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelTypeTrivialSplitPlaceSupport
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.R3.LiftBrg.SplitChi

theorem chi_loc_lift : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (j : (envL X I hX U Xg tr L cV i t).lev.J) (hj : (envL X I hX U Xg tr L cV i t).isLoc x j),
    (envL X I hX U Xg tr L cV i t).lev.χ j = 1 := by
  intro X px I hX U Xg tr L hI hV hL cV i t x j hj
  set P0 : Formalism.L2.DIV.Pl X.toD7.host.E := x.1.1.1 with hP0
  have hoff : P0 ∈ Formalism.L2.DIV.offSet ∅ (sgL X I U t) ∅ := x.1.2
  have e : (envL X I hX U Xg tr L cV i t).lev.χ j = Formalism.L2.DIV.levFn (L.βV i) (flag1L (L.datVt i t))
      (Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1) := rfl
  have hm : Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1 ∈
      Formalism.L2.DIV.lev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (flag1L (L.datVt i t)) := j.2
  have hSt := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hm)
  have hj' : isLocEnv (Vc X.toD7 i) (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t) x
      (j : Bridge.Gf (Vc X.toD7 i)) := hj
  have hle : IsLocElt (Vc X.toD7 i) P0 (j : Bridge.Gf (Vc X.toD7 i)) := by
    obtain ⟨e, α, he, hα, hs, hx⟩ := hj'
    exact ⟨e, e + cA X.toD7 e, α, Or.inl ⟨he, rfl⟩, hα, hx, hs⟩
  have hloc := GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt (Vc X.toD7 i) _ _ hle
  have hnot : P0 ∉ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := fun h => hoff.2.1 (Or.inr h)
  have hnotc : ∀ PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1, PP ≠ Formalism.DivisionValues.conjPl P0 := by
    intro PP hPP h
    apply hoff.2.2 PP (Or.inr hPP)
    rw [Formalism.L2.Col.conjIdeal_asIdeal, GlobalTheory.PlaceDict.conjP_eq_conjPl X.toD7, h]
  have hunder : ∀ PP : Formalism.L2.DIV.Pl X.toD7.host.E, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 →
      PP.under (𝓞 X.toD7.host.F) ≠ P0.under (𝓞 X.toD7.host.F) := by
    intro PP hPP hu
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with h | h
    · exact hnot (h ▸ hPP)
    · exact hnotc PP hPP h
  have hred : ∀ PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1,
      Formalism.L2.DIV.redFn (L.βV i) PP (Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1) = 1 :=
    fun PP hPP => GlobalTheory.Mem.R3.LiftInertChi.redFn_eq_one_of_locAt _ _ hSt _ hloc PP (hunder PP hPP)
  have hPg : ∀ PP ∈ (flag1L (L.datVt i t)).Pg, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L (L.datVt i t)).Pg = L.Pg from rfl, hL.Pg] at hPP
    classical
    exact Finset.mem_union.2 (Or.inl hPP)
  have hQ : ∀ PP ∈ (flag1L (L.datVt i t)).Q, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L (L.datVt i t)).Q = L.Q t from rfl, hL.Q t] at hPP
    have e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1 := by
      simp only [ColIn.Q, tup_ixOf]
    rw [e4] at hPP
    classical
    exact Finset.mem_union.2 (Or.inr hPP)
  rw [e]
  exact GlobalTheory.LevSplit.levFn_eq_one _ _ _ fun PP hPP => hred PP (hPP.elim (hPg PP) (hQ PP))

end GlobalTheory.Mem.R3.LiftBrg.SplitChi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestVectorEvaluationIdentifiesLevelRowsConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe


set_option maxHeartbeats 1000000 in
theorem evalOn_all : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ ∃ c : ℝ, 0 < c ∧ EvalOn R X h t v₀ c (MultR R F) (conjRows X) := by
  intro hDS hCusp hU hFin D G' _ _ Pl0 T A Ks _ _ _ R F X h t hE hGap hl hi hν hsee
  obtain ⟨cc, hcc, hsm⟩ := _root_.GlobalTheory.ConjVecLow.conjModel_of_gap hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee
  let v₀ : (MP R).Vec := fun τ => ⟨(cc τ).symm (X.B.w (X.pl.symm τ)), hsm τ⟩
  have hv₀ : ∀ τ, cc τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ) := fun τ => by simp [v₀]
  have hnorm : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1 := fun τ => by
    show ‖(cc τ).symm (X.B.w (X.pl.symm τ))‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact (X.low _).1
  obtain ⟨c0, hc0, hN⟩ := _root_.GlobalTheory.EvalAllRows.evalTranslate_norm_all hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee
  have hI := _root_.GlobalTheory.Mem.SRe.conj_ev_mem_HHX hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee cc v₀ hcc hv₀
  have hO := _root_.GlobalTheory.Mem.SRe.exists_multR_eval_of_star_mem hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee cc v₀ hcc hv₀
  refine ⟨v₀, hnorm, c0, hc0, ?_⟩
  classical
  have hmem : ∀ S : MultR R F, MemLp (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) 2 (muX X) :=
    fun S => (hN v₀ hnorm S S.2).1
  let Φ : MultR R F → conjRows X := fun S =>
    ⟨(hmem S).toLp _, hI S S.2 _ (hmem S).coeFn_toLp⟩
  have hΦ : ∀ S, ((Φ S : conjRows X) : L2X X) =ᵐ[muX X]
      (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) := fun S => (hmem S).coeFn_toLp
  have key : ∀ (S : MultR R F) (Fx : conjRows X), ((Fx : L2X X) =ᵐ[muX X]
      fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) → Φ S = Fx := by
    intro S Fx hF
    apply Subtype.ext
    apply Lp.ext
    exact (hΦ S).trans hF.symm
  let L : MultR R F →ₗ[ℂ] conjRows X :=
    { toFun := Φ
      map_add' := fun S S' => by
        apply key
        have h1 := hΦ S
        have h2 := hΦ S'
        have h3 := Lp.coeFn_add ((Φ S : conjRows X) : L2X X) ((Φ S' : conjRows X) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.add h2))).trans ?_
        · simp only [Submodule.coe_add]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply]
      map_smul' := fun a S => by
        rw [RingHom.id_apply]
        apply key
        have h1 := hΦ S
        have h3 := Lp.coeFn_smul a ((Φ S : conjRows X) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.const_smul a))).trans ?_
        · simp only [Submodule.coe_smul]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply] }
  have hLn : ∀ S : MultR R F, ‖((L S : conjRows X) : L2X X)‖ ^ 2 =
      c0 * (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re := by
    intro S
    show ‖((hmem S).toLp _ : L2X X)‖ ^ 2 = _
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp (hmem S)]
    exact (hN v₀ hnorm S S.2).2.1
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro S hS
    have h1 := hLn S
    rw [hS] at h1
    simp only [ZeroMemClass.coe_zero, norm_zero, zero_pow two_ne_zero] at h1
    have h2 := (mul_eq_zero_iff_left hc0.ne').mp h1.symm
    exact Subtype.ext ((hN v₀ hnorm S S.2).2.2 h2)
  have hsurj : Function.Surjective L := by
    intro Fx
    obtain ⟨S, hS, hF⟩ := hO (Fx : L2X X) Fx.2
    exact ⟨⟨S, hS⟩, key ⟨S, hS⟩ Fx hF⟩
  refine ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun S => ⟨hΦ S, hLn S⟩⟩

end GlobalTheory.Mem.SRe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberTopFinalContextParameters
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem memberTop_final_contextParameters :
    StandardLattice.SiegelMassRatioCM → (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) →
    ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot) (QO : Par → ∀ D : D7, Obj D → Prop),
      GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' →
      (EvP fun κ K => ∀ β : BPt K, β.Is Q' → QO κ β.D β.O) →
      RecExP (fun κ => DQ.withQD (fun D O => κ.Pos → QO κ D O)) :=
  fun hAll hU KP Q Q' QO hB hF hE hS hEv =>
    _root_.GlobalTheory.Fc.recExP_of_recAtG hAll Q' QO
      (_root_.GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes (GlobalTheory.Mem.VolMass.volumes_eq_masses_of_unfold hU) KP Q Q' hB hF hE hS)
      hEv

end GlobalTheory.Fc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointOverXHasAdelicPointBlockExtendMulStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointOverX_has_adelicPoint_blockExtend_mul : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → Pins B X → ∀ (l : I.Laws) (Z : Later B (I.cols l)) (u : B.Word) (a : I.ι) (k t : GA B (B.R.N B.R.m)), (∃ p : DecoF B.fields.E (B.R.N B.R.m) ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N B.R.m)) → (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) → (∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N B.R.m)), r.1 + 1 = (B.R.N B.R.m) → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)) → t ∈ K1 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs → (∀ (P : I.Q a) (i j : Fin (B.R.N B.R.m)), adAt B.host.F P.1 (t.1 i j) = algebraMap B.host.E _ (if i = j then (if i.1 + 1 = (B.R.N B.R.m) then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0)) → ∀ (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d → IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 → PtOf (g * (k * t)) (tilF I.sel (I.tup a) u d) := by
  first | exact @GlobalTheory.Mem.Col2.TilQ.pt_tilF_gen | exact GlobalTheory.Mem.Col2.TilQ.pt_tilF_gen | (intros; apply GlobalTheory.Mem.Col2.TilQ.pt_tilF_gen <;> assumption)
end

