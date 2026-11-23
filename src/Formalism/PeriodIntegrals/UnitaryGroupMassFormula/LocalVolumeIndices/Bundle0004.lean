module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.HelpSng
section
noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain
open Formalism.MainNotions.S (AutInst)

variable (I : AutInst) (p : HeightOneSpectrum (𝓞 I.F))

abbrev eP : Af I.F ⊗[I.F] I.E := chi I p ⊗ₜ[I.F] (1 : I.E)

theorem HelpSng_sL_mul (a b : Fv I.F p) : sL I p (a * b) = sL I p a * sL I p b := by
  show singleV I.F p (a * b) = singleV I.F p a * singleV I.F p b
  apply FiniteAdeleRing.ext; intro v
  rw [Comp_mul_apply]
  by_cases h : v = p
  · subst h; simp only [Comp_single_same]
  · simp only [Comp_single_ne I p v h, mul_zero]

private theorem localTheta_tmul (a : Fv I.F p) (b : I.E) :
    thetaP I p (a ⊗ₜ[I.F] b) = sL I p a ⊗ₜ[I.F] b := rfl

theorem HelpSng_theta_mul (x y : Fv I.F p ⊗[I.F] I.E) :
    thetaP I p (x * y) = thetaP I p x * thetaP I p y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_mul, map_zero]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [mul_zero, map_zero]
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, localTheta_tmul, localTheta_tmul, localTheta_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, HelpSng_sL_mul]
    | add y1 y2 h1 h2 => simp only [mul_add, map_add (f := _), h1, h2]
  | add x1 x2 h1 h2 => simp only [add_mul, map_add (f := _), h1, h2]

theorem HelpSng_theta_one : thetaP I p 1 = eP I p := by
  rw [Algebra.TensorProduct.one_def, localTheta_tmul]
  rfl

theorem HelpSng_theta_inclR (x : I.E) :
    thetaP I p (inclR (Fv I.F p) x) = eP I p * inclR (Af I.F) x := by
  have h1 : inclR (Fv I.F p) x = (1 : Fv I.F p) ⊗ₜ[I.F] x := rfl
  have h2 : inclR (Af I.F) x = (1 : Af I.F) ⊗ₜ[I.F] x := rfl
  rw [h1, h2, localTheta_tmul]
  show sL I p 1 ⊗ₜ[I.F] x = (chi I p ⊗ₜ[I.F] (1 : I.E)) * ((1 : Af I.F) ⊗ₜ[I.F] x)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

private theorem tensMap_tmul_lemma_2 (v : HeightOneSpectrum (𝓞 I.F)) (a : Af I.F) (b : I.E) :
    tensMap (E := I.E) (evalV I.F v) (a ⊗ₜ[I.F] b) = evalV I.F v a ⊗ₜ[I.F] b := rfl

theorem HelpSng_eval_theta (t : Fv I.F p ⊗[I.F] I.E) :
    tensMap (E := I.E) (evalV I.F p) (thetaP I p t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [localTheta_tmul, tensMap_tmul_lemma_2]
    show singleV I.F p a p ⊗ₜ[I.F] b = a ⊗ₜ[I.F] b
    rw [Comp_single_same]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem HelpSng_eval_theta_ne (v : HeightOneSpectrum (𝓞 I.F)) (hv : v ≠ p) (t : Fv I.F p ⊗[I.F] I.E) :
    tensMap (E := I.E) (evalV I.F v) (thetaP I p t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [localTheta_tmul, tensMap_tmul_lemma_2]
    show singleV I.F p a v ⊗ₜ[I.F] b = 0
    rw [Comp_single_ne I p v hv, TensorProduct.zero_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]

theorem HelpSng_eval_e : tensMap (E := I.E) (evalV I.F p) (eP I p) = 1 := by
  show tensMap (E := I.E) (evalV I.F p) (chi I p ⊗ₜ[I.F] (1 : I.E)) = 1
  rw [tensMap_tmul_lemma_2]
  show singleV I.F p 1 p ⊗ₜ[I.F] (1 : I.E) = 1
  rw [Comp_single_same, Algebra.TensorProduct.one_def]

theorem HelpSng_eval_e_ne (v : HeightOneSpectrum (𝓞 I.F)) (hv : v ≠ p) :
    tensMap (E := I.E) (evalV I.F v) (eP I p) = 0 := by
  show tensMap (E := I.E) (evalV I.F v) (chi I p ⊗ₜ[I.F] (1 : I.E)) = 0
  rw [tensMap_tmul_lemma_2]
  show singleV I.F p 1 v ⊗ₜ[I.F] (1 : I.E) = 0
  rw [Comp_single_ne I p v hv, TensorProduct.zero_tmul]

theorem HelpSng_e_theta (t : Fv I.F p ⊗[I.F] I.E) : eP I p * thetaP I p t = thetaP I p t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero]
  | tmul a b =>
    rw [localTheta_tmul]
    show (chi I p ⊗ₜ[I.F] (1 : I.E)) * (sL I p a ⊗ₜ[I.F] b) = sL I p a ⊗ₜ[I.F] b
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, show chi I p = sL I p 1 from rfl,
      ← HelpSng_sL_mul, one_mul]
  | add x y hx hy => simp only [mul_add, map_add (f := _), hx, hy]

theorem idempotent_complement_mul (t : Fv I.F p ⊗[I.F] I.E) : (1 - eP I p) * thetaP I p t = 0 := by
  rw [sub_mul, one_mul, HelpSng_e_theta, sub_self]

theorem HelpSng_e_idem : eP I p * eP I p = eP I p := by
  have h := HelpSng_e_theta I p 1
  rwa [HelpSng_theta_one] at h

theorem idempotent_complement_idem : (1 - eP I p) * (1 - eP I p) = 1 - eP I p := by
  rw [sub_mul, one_mul, mul_sub, mul_one, HelpSng_e_idem, sub_self, sub_zero]

private theorem sigR_tmul_lemma_3 {R : Type} [CommRing R] [Algebra I.F R] (a : R) (b : I.E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R I.cm.sig (a ⊗ₜ[I.F] b) = a ⊗ₜ[I.F] I.cm.sig b := rfl

theorem HelpSng_sig_e : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig (eP I p) = eP I p := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig (chi I p ⊗ₜ[I.F] (1 : I.E)) = chi I p ⊗ₜ[I.F] (1 : I.E)
  rw [sigR_tmul_lemma_3, map_one]

theorem HelpSng_sig_theta (t : Fv I.F p ⊗[I.F] I.E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig (thetaP I p t) = thetaP I p (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv I.F p) I.cm.sig t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rw [localTheta_tmul, sigR_tmul_lemma_3, sigR_tmul_lemma_3, localTheta_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def mixM {m o : Type} (A : Matrix m o (Af I.F ⊗[I.F] I.E)) (K : Matrix m o (Fv I.F p ⊗[I.F] I.E)) :
    Matrix m o (Af I.F ⊗[I.F] I.E) :=
  (1 - eP I p) • A + K.map (thetaP I p)

theorem HelpSng_mix_mul {m o q : Type} [Fintype o] (A : Matrix m o (Af I.F ⊗[I.F] I.E))
    (K : Matrix m o (Fv I.F p ⊗[I.F] I.E)) (B : Matrix o q (Af I.F ⊗[I.F] I.E))
    (L : Matrix o q (Fv I.F p ⊗[I.F] I.E)) :
    mixM I p A K * mixM I p B L = mixM I p (A * B) (K * L) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mixM, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    map_sum, Finset.mul_sum, HelpSng_theta_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  linear_combination (A i k * B k j) * idempotent_complement_idem I p + A i k * idempotent_complement_mul I p (L k j) +
    B k j * idempotent_complement_mul I p (K i k)

theorem HelpSng_mix_one {m : Type} [DecidableEq m] :
    mixM I p (1 : Matrix m m (Af I.F ⊗[I.F] I.E)) (1 : Matrix m m (Fv I.F p ⊗[I.F] I.E)) = 1 := by
  ext i j
  simp only [mixM, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs
  · rw [HelpSng_theta_one]; ring
  · rw [map_zero]; ring

theorem HelpSng_JR_split :
    mixM I p (JR (Af I.F) I.J) (JR (Fv I.F p) I.J) = JR (Af I.F) I.J := by
  ext i j
  show (1 - eP I p) * inclR (Af I.F) (I.J i j) + thetaP I p (inclR (Fv I.F p) (I.J i j)) =
    inclR (Af I.F) (I.J i j)
  rw [HelpSng_theta_inclR]
  ring

theorem HelpSng_cT_mix {m o : Type} (A : Matrix m o (Af I.F ⊗[I.F] I.E))
    (K : Matrix m o (Fv I.F p ⊗[I.F] I.E)) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig) (mixM I p A K) =
      mixM I p (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig) A) (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv I.F p) I.cm.sig) K) := by
  ext i j
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig (mixM I p A K j i) = mixM I p (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig) A)
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv I.F p) I.cm.sig) K) i j
  simp only [mixM, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_add (f := _), map_mul,
    map_sub, map_one, HelpSng_sig_e, HelpSng_sig_theta]
  rfl

theorem HelpSng_cT_one :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig) (1 : Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) = 1 := by
  show ((1 : Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig))ᵀ = 1
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

def sngGL (k : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) : GL (Fin I.n) (Af I.F ⊗[I.F] I.E) where
  val := mixM I p 1 (k : Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E))
  inv := mixM I p 1 ((k⁻¹ : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) : Matrix (Fin I.n) (Fin I.n) _)
  val_inv := by rw [HelpSng_mix_mul, Matrix.one_mul, Units.mul_inv, HelpSng_mix_one]
  inv_val := by rw [HelpSng_mix_mul, Matrix.one_mul, Units.inv_mul, HelpSng_mix_one]

theorem HelpSng_unitary (k : HA (Fv I.F p) I.cm.sig I.J) :
    sngGL I p (HA.mat (Fv I.F p) I.cm.sig I.J k) ∈ HR (Af I.F) I.cm.sig I.J := by
  have hK : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv I.F p) I.cm.sig)
      ((HA.mat (Fv I.F p) I.cm.sig I.J k : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) * JR (Fv I.F p) I.J *
      ((HA.mat (Fv I.F p) I.cm.sig I.J k : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) = JR (Fv I.F p) I.J := k.2
  show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af I.F) I.cm.sig) (mixM I p 1 _) * JR (Af I.F) I.J * mixM I p 1 _ = JR (Af I.F) I.J
  conv_lhs => rw [← HelpSng_JR_split I p]
  rw [HelpSng_cT_mix, HelpSng_mix_mul, HelpSng_mix_mul, hK, HelpSng_cT_one, Matrix.one_mul,
    Matrix.mul_one, HelpSng_JR_split]

def sngHA (k : HA (Fv I.F p) I.cm.sig I.J) : HA (Af I.F) I.cm.sig I.J :=
  ⟨sngGL I p (HA.mat (Fv I.F p) I.cm.sig I.J k), HelpSng_unitary I p k⟩

theorem HelpSng_piV_same (k : HA (Fv I.F p) I.cm.sig I.J) : piV I p (sngHA I p k) = k := by
  apply Subtype.ext
  apply Units.ext
  show (mixM I p 1 ((HA.mat (Fv I.F p) I.cm.sig I.J k : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E))).map (tensMap (E := I.E) (evalV I.F p)) =
    ((HA.mat (Fv I.F p) I.cm.sig I.J k : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E))
  ext i j
  simp only [Matrix.map_apply, mixM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
    map_sub, map_one, HelpSng_eval_e, HelpSng_eval_theta, sub_self, zero_mul, zero_add]

theorem HelpSng_piV_ne (k : HA (Fv I.F p) I.cm.sig I.J) (v : HeightOneSpectrum (𝓞 I.F)) (hv : v ≠ p) :
    piV I v (sngHA I p k) = 1 := by
  apply Subtype.ext
  apply Units.ext
  show (mixM I p 1 ((HA.mat (Fv I.F p) I.cm.sig I.J k : GL (Fin I.n) (Fv I.F p ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Fv I.F p ⊗[I.F] I.E))).map (tensMap (E := I.E) (evalV I.F v)) = 1
  ext i j
  simp only [Matrix.map_apply, mixM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
    map_sub, map_one, HelpSng_eval_e_ne I p v hv, HelpSng_eval_theta_ne I p v hv, sub_zero, one_mul,
    add_zero]
  rcases eq_or_ne i j with h | h <;> simp [Matrix.one_apply, h]

theorem HelpSng_mem_Kf (k : HA (Fv I.F p) I.cm.sig I.J)
    (hk : k ∈ Kv I.cm.sig I.J (I.L : Set (Fin I.n → I.E)) p) :
    sngHA I p k ∈ Kf I.cm.sig I.J (I.L : Set (Fin I.n → I.E)) := by
  refine Subgroup.mem_iInf.mpr (fun v => ?_)
  show HA.mat (Fv I.F v) I.cm.sig I.J (piV I v (sngHA I p k)) ∈ Kloc v (I.L : Set (Fin I.n → I.E))
  by_cases hv : v = p
  · subst hv
    rw [HelpSng_piV_same]
    exact hk
  · rw [HelpSng_piV_ne I p k v hv]
    exact Subgroup.one_mem _

theorem single_component_surjective : SngSurj := by
  intro I p k hk
  exact ⟨sngHA I p k, HelpSng_mem_Kf I p k hk, HelpSng_piV_same I p k, fun v hv => HelpSng_piV_ne I p k v hv⟩

end PI.MassDataKppVolLemmas
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.IdxProd
section
noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField IsDedekindDomain
  Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open Formalism.MainNotions.S (AutInst)

theorem index_pi₂ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  classical
  show Nat.card ((∀ i, G i) ⧸ Subgroup.pi Set.univ H) = ∏ i, Nat.card (G i ⧸ H i)
  rw [← Nat.card_pi]
  refine Nat.card_congr (Equiv.ofBijective
    (fun q => Quotient.liftOn' q (fun g i => (QuotientGroup.mk (g i) : G i ⧸ H i)) ?_) ⟨?_, ?_⟩)
  · intro a b hab
    funext i
    rw [QuotientGroup.eq]
    have h1 : a⁻¹ * b ∈ Subgroup.pi Set.univ H := QuotientGroup.leftRel_apply.mp hab
    exact (Subgroup.mem_pi _).mp h1 i (Set.mem_univ i)
  · intro q q' h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q'
    rw [QuotientGroup.eq, Subgroup.mem_pi]
    intro i _
    exact QuotientGroup.eq.mp (congrFun h i)
  · intro f
    refine ⟨QuotientGroup.mk (fun i => (f i).out), ?_⟩
    funext i
    exact QuotientGroup.out_eq' (f i)

def KsetSub (I : AutInst) : Subgroup I.Gf :=
  (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def levelSubgroupOfCharacter (hK : X.LevelSubgroupCharacter) : Subgroup X.B.I.Gf where
  carrier := X.K2
  one_mem' := hK.1
  mul_mem' {a b} ha hb := hK.2.1 a ha b hb
  inv_mem' {a} ha := hK.2.2.1 a ha

theorem IP_K2HA_eq : levelUnitary X hb = tf X.B.I hb '' X.K2 := rfl

theorem IP_KppS (hK : X.LevelSubgroupCharacter) : KppS X hb = (levelSubgroupOfCharacter X hK).map (tfHom X.B.I hb) := by
  rw [← Subgroup.closure_eq (levelSubgroupOfCharacter X hK), MonoidHom.map_closure]
  rfl

theorem IP_KfS : KfS X = (KsetSub X.B.I).map (tfHom X.B.I hb) := by
  ext h
  rw [Subgroup.mem_map]
  constructor
  · intro hh
    obtain ⟨x, rfl⟩ := Bridge_tf_surjective X.B.I hb h
    exact ⟨x, (Bridge_mem_Kf_iff X.B.I hb x).1 hh, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (Bridge_mem_Kf_iff X.B.I hb x).2 hx

theorem IP_gIdx (hK : X.LevelSubgroupCharacter) : gIdx X hb = (levelSubgroupOfCharacter X hK).relIndex (KsetSub X.B.I) := by
  rw [gIdx, IP_KppS X hb hK, IP_KfS X hb]
  exact Subgroup.relIndex_map_map_of_injective _ _ (Bridge_tf_injective X.B.I hb)

def KvSub (p : TypX X) : Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) :=
  (Kloc p.1 (lamS X)).comap (HR (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J).subtype

theorem IP_KvS (p : TypX X) : KvS X p = KvSub X p := by
  rw [KvS]
  exact Subgroup.closure_eq (KvSub X p)

theorem piV_mem_KvS (p : TypX X) (x : X.B.I.Gf) (hx : x ∈ X.B.I.Kset) :
    piV X.B.I p.1 (tf X.B.I hb x) ∈ KvS X p := by
  rw [IP_KvS]
  have h := (Bridge_mem_Kf_iff X.B.I hb x).2 hx
  rw [Kf, Subgroup.mem_iInf] at h
  exact h p.1

def phiK : KsetSub X.B.I →* ∀ p : TypX X, KvS X p :=
  MonoidHom.pi fun p => MonoidHom.codRestrict
    (((piV X.B.I p.1).comp (tfHom X.B.I hb)).comp (KsetSub X.B.I).subtype) (KvS X p)
    (fun x => piV_mem_KvS X hb p x.1 x.2)

theorem phiK_apply₂ (x : KsetSub X.B.I) (p : TypX X) :
    ((phiK X hb x p : KvS X p) : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) = piV X.B.I p.1 (tf X.B.I hb x.1) := rfl

theorem IP_KppvS (hK : X.LevelSubgroupCharacter) (p : TypX X) :
    KppvS X hb p = (levelSubgroupOfCharacter X hK).map ((piV X.B.I p.1).comp (tfHom X.B.I hb)) := by
  rw [KppvS]
  have : compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1 =
      ((levelSubgroupOfCharacter X hK).map ((piV X.B.I p.1).comp (tfHom X.B.I hb)) : Set _) := by
    rw [Subgroup.coe_map, compSet, IP_K2HA_eq, Set.image_image]; rfl
  rw [this, Subgroup.closure_eq]

theorem g_ne_zero₂ (i : Fin 2) : D.host.g i ≠ 0 := (D.host.g_prime i).ne_zero

theorem levelSubgroupAlt_subgroupOf_eq_comap_pi (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) :
    (levelSubgroupOfCharacter X hK).subgroupOf (KsetSub X.B.I) =
      (Subgroup.pi Set.univ fun p => (KppvS X hb p).subgroupOf (KvS X p)).comap (phiK X hb) := by
  ext ⟨z, hz⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, Subgroup.mem_subgroupOf, phiK_apply₂, IP_KppvS X hb hK,
    Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply, Bridge_tfHom_apply]
  constructor
  · intro h p
    exact ⟨z, h, rfl⟩
  · intro h
    have hgc := Cst_gc X.B.I (D.host.g 0) (D.host.g 1) (g_ne_zero₂ (D := D) 0) (g_ne_zero₂ (D := D) 1)
    rw [← X.g_eq] at hgc
    refine LocK_mem X.B.I X.K2 hK.1 hK.2.1 X.B.g (fun x hx => (hL.1 x hx).1) Finset.univ
      (fun p : TypX X => chi X.B.I p.1) (fun p => Comp_chi_idem X.B.I p.1)
      (fun p q hpq => Comp_chi_orth X.B.I p.1 q.1 fun h => hpq (Subtype.ext h))
      (cElt X.B.I (D.host.g 0) (D.host.g 1)) (Cst_int X.B.I _ _) hgc z hz ?_
    intro p _
    obtain ⟨w, hw, hwz⟩ := h p
    rw [Comp_sep X.B.I hb p.1 z w hwz.symm]
    exact LocB_K2set X.B.I _ _ _ _ _ (Comp_chi_idem X.B.I p.1) (Comp_chi_int X.B.I p.1) w hw

theorem phiK_surjective (hS : SngSurj) : Function.Surjective (phiK X hb) := by
  classical
  intro f
  have key : ∀ S : Finset (TypX X), ∃ z : KsetSub X.B.I, ∀ p,
      (phiK X hb z p : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) = if p ∈ S then (f p : _) else 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, fun p => by simp⟩
    | insert q S hq ih =>
      obtain ⟨z, hz⟩ := ih
      have hfq : ((f q : KvS X q) : HA (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J) ∈
          Kv X.B.I.cm.sig X.B.I.J (lamS X) q.1 := by
        have h2 : ∀ x, x ∈ KvS X q → x ∈ Kv X.B.I.cm.sig X.B.I.J (lamS X) q.1 := fun x hx => by
          rw [IP_KvS] at hx; exact hx
        exact h2 _ (f q).2
      obtain ⟨h, hKf, hq1, hq2⟩ := hS X.B.I q.1 _ hfq
      obtain ⟨y, rfl⟩ := Bridge_tf_surjective X.B.I hb h
      have hy : y ∈ KsetSub X.B.I := (Bridge_mem_Kf_iff X.B.I hb y).1 hKf
      refine ⟨⟨y, hy⟩ * z, fun p => ?_⟩
      rw [map_mul, Pi.mul_apply, Subgroup.coe_mul, hz p, phiK_apply₂]
      by_cases hpq : p = q
      · subst hpq
        rw [if_neg hq, if_pos (Finset.mem_insert_self p S), Subgroup.coe_one, mul_one]
        exact hq1
      · have hp1 : p.1 ≠ q.1 := fun h => hpq (Subtype.ext h)
        rw [hq2 p.1 hp1, one_mul]
        by_cases hpS : p ∈ S
        · rw [if_pos hpS, if_pos (Finset.mem_insert_of_mem hpS)]
        · rw [if_neg hpS, if_neg]
          intro hm
          rcases Finset.mem_insert.1 hm with h' | h'
          · exact hpq h'
          · exact hpS h'
  obtain ⟨z, hz⟩ := key Finset.univ
  refine ⟨z, funext fun p => Subtype.ext ?_⟩
  rw [hz p, if_pos (Finset.mem_univ p)]

theorem IP_idxProd (hS : SngSurj) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized) : IdxProd X hb := by
  show gIdx X hb = ∏ p : TypX X, lIdx X hb p
  rw [IP_gIdx X hb hK]
  show ((levelSubgroupOfCharacter X hK).subgroupOf (KsetSub X.B.I)).index = _
  rw [levelSubgroupAlt_subgroupOf_eq_comap_pi X hb hK hL, Subgroup.index_comap_of_surjective (hf := phiK_surjective X hb hS), index_pi₂]
  rfl

theorem idxProdAll_of (hS : SngSurj) : IdxProdAll := by
  intro D X hb hK _ hL
  exact IP_idxProd X hb hS hK hL

end PI.MassDataKppVolLemmas
end
end

