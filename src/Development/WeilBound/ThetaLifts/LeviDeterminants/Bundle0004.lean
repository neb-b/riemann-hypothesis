module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmAlgebraSplitInvolution
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.ExistsScaledIntegralLatticeSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.DoubledUnitaryCharacterTrivialOfSiegel
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

noncomputable section

namespace PositivityTheory.ThKF0.Sg

section Split

variable {F A R₁ R₂ : Type} (E : Type) [Field F] [CommRing A] [Algebra F A] [CommRing R₁] [Algebra F R₁] [CommRing R₂]
  [Algebra F R₂] [CommRing E] [Algebra F E]

def split (s : A ≃ₐ[F] R₁ × R₂) : A ⊗[F] E ≃ₐ[F] (R₁ ⊗[F] E) × (R₂ ⊗[F] E) :=
  (Algebra.TensorProduct.congr s AlgEquiv.refl).trans
    (((Algebra.TensorProduct.comm F (R₁ × R₂) E).trans (Algebra.TensorProduct.prodRight F F E R₁ R₂)).trans
      (AlgEquiv.prodCongr (Algebra.TensorProduct.comm F E R₁) (Algebra.TensorProduct.comm F E R₂)))

variable {E}

theorem split_tmul (s : A ≃ₐ[F] R₁ × R₂) (a : A) (e : E) :
    split E s (a ⊗ₜ[F] e) = ((s a).1 ⊗ₜ[F] e, (s a).2 ⊗ₜ[F] e) := by
  have h : (Algebra.TensorProduct.comm F (R₁ × R₂) E) (s a ⊗ₜ[F] e) = e ⊗ₜ[F] s a := rfl
  have h0 : Algebra.TensorProduct.congr s (AlgEquiv.refl : E ≃ₐ[F] E) (a ⊗ₜ[F] e) = s a ⊗ₜ[F] e := rfl
  simp only [split, AlgEquiv.trans_apply, h0, h, Algebra.TensorProduct.prodRight_tmul]
  rfl

theorem split_conj (s : A ≃ₐ[F] R₁ × R₂) (σ : E →ₐ[F] E) (x : A ⊗[F] E) :
    split E s (Algebra.TensorProduct.map (AlgHom.id A A) σ x) =
      (Algebra.TensorProduct.map (AlgHom.id F R₁) σ (split E s x).1,
        Algebra.TensorProduct.map (AlgHom.id F R₂) σ (split E s x).2) := by
  induction x using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, split_tmul, split_tmul]
    rfl
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
    simp

end Split

section Piece

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {c : S →ₐ[R] S} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mix_mul {f : S} (hf : f * f = f) (A B C D : Matrix ι ι S) :
    (f • A + (1 - f) • B) * (f • C + (1 - f) • D) = f • (A * C) + (1 - f) • (B * D) := by
  have h1 : f * (1 - f) = 0 := by linear_combination -hf
  have h2 : (1 - f) * f = 0 := by linear_combination -hf
  have h3 : (1 - f) * (1 - f) = 1 - f := by linear_combination hf
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hf, h1, h2, h3,
    zero_smul, add_zero, zero_add]

theorem mix_self (f : S) (A : Matrix ι ι S) : f • A + (1 - f) • A = A := by
  rw [← add_smul, add_sub_cancel, one_smul]

def piece {J : Matrix ι ι S} {f : S} (hf : f * f = f) (hc : c f = f) (g : UG c J) : UG c J :=
  ⟨⟨f • g.1.1 + (1 - f) • 1, f • (g.1⁻¹).1 + (1 - f) • 1, by rw [mix_mul hf, Units.mul_inv, mul_one, mix_self],
    by rw [mix_mul hf, Units.inv_mul, mul_one, mix_self]⟩, by
    have hg : (g.1.1)ᵀ * J * (g.1.1).map c = J := g.2
    change (f • g.1.1 + (1 - f) • 1)ᵀ * J * (f • g.1.1 + (1 - f) • (1 : Matrix ι ι S)).map c = J
    have e : (f • g.1.1 + (1 - f) • (1 : Matrix ι ι S)).map c = f • (g.1.1).map c + (1 - f) • 1 := by
      ext i j
      by_cases h : i = j <;> simp [hc, Matrix.one_apply, h]
    rw [e, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one]
    have k : ∀ A B : Matrix ι ι S, (f • A + (1 - f) • 1) * J * (f • B + (1 - f) • 1) = f • (A * J * B) + (1 - f) • J :=
      fun A B => by
        conv_lhs => rw [← mix_self f J]
        rw [mix_mul hf, mix_mul hf, one_mul, mul_one]
    rw [k, hg, mix_self]⟩

end Piece

variable {F : Type} [Field F] [NumberField F]

open GlobalTheory.LocalGlobalChar


variable (F) in
abbrev RS (S : Finset (HeightOneSpectrum (𝓞 F))) : Type := Ainf F × ((v : S) → Fv F v.1)

def toRS (S : Finset (HeightOneSpectrum (𝓞 F))) : AF F →ₐ[F] RS F S :=
  (AlgHom.fst F (Ainf F) (Af F)).prod (Pi.algHom F _ fun v : S => (evalV F v.1).comp (AlgHom.snd F (Ainf F) (Af F)))

theorem toRS_eps (S : Finset (HeightOneSpectrum (𝓞 F))) : toRS S (eps S) = 1 := by
  refine Prod.ext rfl (funext fun v => ?_)
  change evalV F v.1 (ind S) = 1
  rw [ev_ind, if_pos v.2]

theorem eps_mul_of (S : Finset (HeightOneSpectrum (𝓞 F))) {a : AF F} (h : toRS S a = 0) : eps S * a = 0 := by
  have h1 : a.1 = 0 := congrArg Prod.fst h
  refine Prod.ext ?_ (fin_ext fun u => ?_)
  · change 1 * a.1 = 0
    rw [h1, mul_zero]
  · change evalV F u (ind S * a.2) = evalV F u 0
    rw [map_mul, ev_ind, map_zero]
    split_ifs with hu
    · have h2 : evalV F u a.2 = 0 := congrFun (congrArg Prod.snd h) ⟨u, hu⟩
      rw [h2, mul_zero]
    · rw [zero_mul]

theorem toRS_surj (S : Finset (HeightOneSpectrum (𝓞 F))) : Function.Surjective (toRS S) := by
  classical
  intro r
  let y : Af F := ⟨fun u => if h : u ∈ S then r.2 ⟨u, h⟩ else 0, by
    refine Filter.eventually_cofinite.mpr (S.finite_toSet.subset fun v hv => ?_)
    by_contra hvS
    apply hv
    have hvS' : v ∉ S := fun h => hvS (Finset.mem_coe.mpr h)
    beta_reduce
    rw [dite_eq_right hvS']
    exact zero_mem (v.adicCompletionIntegers F)⟩
  refine ⟨pairA F r.1 y, Prod.ext rfl (funext fun v => ?_)⟩
  exact dif_pos v.2

def splitS (S : Finset (HeightOneSpectrum (𝓞 F))) : AF F ≃ₐ[F] RS F S × (AF F ⧸ Ideal.span {eps S}) :=
  AlgEquiv.ofBijective ((toRS S).prod (Ideal.Quotient.mkₐ F _)) ⟨by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have h1 : toRS S a = 0 := congrArg Prod.fst ha
    have h2 : Ideal.Quotient.mk (Ideal.span {eps S}) a = 0 := congrArg Prod.snd ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
    have h3 := eps_mul_of S h1
    rwa [mul_left_comm, eps_mul_self] at h3, by
    rintro ⟨r, q⟩
    obtain ⟨a, rfl⟩ := toRS_surj S r
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h0 : Ideal.Quotient.mk (Ideal.span {eps S}) (eps S) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    refine ⟨eps S * a + (1 - eps S) * b, Prod.ext ?_ ?_⟩
    · change toRS S _ = toRS S a
      rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, toRS_eps]
      ring
    · change Ideal.Quotient.mk (Ideal.span {eps S}) _ = Ideal.Quotient.mk (Ideal.span {eps S}) b
      rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, h0]
      ring⟩

theorem splitS_eps (S : Finset (HeightOneSpectrum (𝓞 F))) : (splitS S (eps S)).2 = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem triv_piece (hσ : IsCMExt F E σ) {β : Type} [Fintype β] [DecidableEq β] (J : Matrix β β (AE F E)) (hJ : IsUnit J.det)
    (lam : UG (cA σ) (dbl J) →* ℂˣ)
    (h : ∀ (p : UG (cA σ) (dbl J)) (t : GL β (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols β = diagCols β * t.1 → lam p = 1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (g : UG (cA σ) (dbl J))
    (hg : ∀ i j, ∃ y, (g.1.1 - 1 : Matrix _ _ (AE F E)) i j = algebraMap (AF F) (AE F E) (eps S) * y) : lam g = 1 := by
  obtain ⟨x, hx⟩ := GlobalTheory.CompanionTheory.Ar.RT.ArchRing.exists_moved hσ
  have hi := GlobalTheory.CompanionTheory.Ar.RT.ArchRing.sigma_invol hσ
  have hξ : x - σ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; omega)
  have : IsArtinianRing (Ainf F) := GlobalTheory.CompanionTheory.Ar.RT.ArchRing.isArtinian_inf
  have : IsArtinianRing (RS F S ⊗[F] E) := IsArtinianRing.of_finite (RS F S) _
  refine _root_.GlobalTheory.CompanionTheory.Ar.RT.CellSplit.char_trivial_first F (AF F) (AE F E) (RS F S ⊗[F] E) ((AF F ⧸ Ideal.span {eps S}) ⊗[F] E) (cA σ)
    (Algebra.TensorProduct.map (AlgHom.id F _) σ) (Algebra.TensorProduct.map (AlgHom.id F _) σ).toRingHom
    (1 ⊗ₜ[F] (x - σ x)) (split E (splitS S)).toRingEquiv ?_ ?_ (fun z => ?_)
    (fun z => congrArg Prod.fst (split_conj (splitS S) σ z)) (fun z => congrArg Prod.snd (split_conj (splitS S) σ z))
    β J hJ lam (fun p t _ _ hpt => h p t hpt) g fun i j => ?_
  · refine IsUnit.of_mul_eq_one ((1 : RS F S) ⊗ₜ[F] (x - σ x)⁻¹) ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hξ]
    rfl
  · rw [Algebra.TensorProduct.map_tmul, map_sub, hi, ← TensorProduct.tmul_neg, neg_sub]
    rfl
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [hi]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  · obtain ⟨y, hy⟩ := hg i j
    change (split E (splitS S) ((g.1.1 - 1 : Matrix _ _ (AE F E)) i j)).2 = 0
    have e : algebraMap (AF F) (AE F E) (eps S) = eps S ⊗ₜ[F] (1 : E) := rfl
    rw [hy, map_mul, Prod.snd_mul, e, split_tmul, splitS_eps, TensorProduct.zero_tmul, zero_mul]

theorem tendsto_mix' {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (AE F E)) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => algebraMap (AF F) (AE F E) (eps S) • M +
      (1 - algebraMap (AF F) (AE F E) (eps S)) • (1 : Matrix ι ι (AE F E))) atTop (𝓝 M) := by
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := (tendsto_eps_tens ((M - 1) i j)).add_const ((1 : Matrix ι ι (AE F E)) i j)
  rw [Matrix.sub_apply, sub_add_cancel] at h
  refine h.congr fun S => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.ThKF0.Sg

open PositivityTheory.ThKF0.Sg GlobalTheory.LocalGlobalChar in
theorem PositivityTheory.ThKF0.local_global_character_interpolation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (AE F E)) (g : UG (cA σ) J₀), ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀, (∀ S, ((q S).1.1 : Matrix ι ι (AE F E)) = algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (AE F E)) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (AE F E))) ∧ Tendsto q atTop (𝓝 g) := by
  intro F E _ _ _ _ _ σ ι _ _ J₀ g
  have he : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), algebraMap (AF F) (AE F E) (eps S) * algebraMap (AF F) (AE F E) (eps S) =
      algebraMap (AF F) (AE F E) (eps S) := fun S => by rw [← map_mul, eps_mul_self]
  refine ⟨fun S => piece (he S) ((cA σ).commutes _) g, fun S => rfl, ?_⟩
  refine (IsEmbedding.subtypeVal.tendsto_nhds_iff).2 ?_
  refine (Units.isEmbedding_embedProduct.tendsto_nhds_iff).2 ?_
  exact (tendsto_mix' g.1.1).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (tendsto_mix' (g.1⁻¹).1))

open PositivityTheory.ThKF0.Sg GlobalTheory.LocalGlobalChar in
theorem PositivityTheory.ThKF0.parabolic_character_trivial_on_diagonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ c : UG (cA σ) (dbl (incM F J)) →* ℂˣ, Continuous c → (∀ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 → c p = 1) → c = 1 := by
  intro F E _ _ _ _ _ σ hσ n J ε _ hdet c hc hP
  have hJ : IsUnit (incM F J).det := by
    have h := (isUnit_iff_ne_zero.mpr hdet).map (inclR (F := F) (AF F))
    rwa [RingHom.map_det] at h
  refine MonoidHom.ext fun g => ?_
  obtain ⟨q, hq, hlim⟩ := PositivityTheory.ThKF0.local_global_character_interpolation F E σ (dbl (incM F J)) g
  have h1 : ∀ S, c (q S) = 1 := fun S => triv_piece hσ _ hJ c hP S (q S) fun i j =>
    ⟨(g.1.1 - 1 : Matrix _ _ (AE F E)) i j, by
      rw [hq S]
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring⟩
  have h2 : Tendsto (fun S => c (q S)) atTop (𝓝 (c g)) := (hc.tendsto g).comp hlim
  simp only [h1] at h2
  exact (tendsto_nhds_unique tendsto_const_nhds h2).symm

end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MCSpan
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.EvAdm

noncomputable section
namespace PositivityTheory.ThKF0.Span
open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_invariant {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∀ x, ∀ z ∈ scaledInt F κ a, g (x + z) = g x := by
  obtain ⟨hlc, hcs⟩ := hg
  have hW : ∀ y, {z | g (y + z) = g y} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) := fun y =>
    ((hlc.isOpen_fiber (g y)).preimage (continuous_const.add continuous_id)).mem_nhds (by simp)
  choose b hb hbW using fun y => PositivityTheory.Mix.exists_scaled_integral_lattice_subset F κ _ (hW y)
  have hN : ∀ y ∈ tsupport g, {x | x - y ∈ scaledInt F κ (b y)} ∈ 𝓝 y := fun y _ =>
    ((isOpen_scaledInt (b y)).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover hcs _ hN
  have hW0 : (⋂ y ∈ t, (scaledInt F κ (b y) : Set (κ → FiniteAdeleRing (𝓞 F) F))) ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
    (Filter.biInter_finset_mem t).2 fun y _ => (isOpen_scaledInt (b y)).mem_nhds (zero_mem _)
  obtain ⟨a, ha, haW⟩ := PositivityTheory.Mix.exists_scaled_integral_lattice_subset F κ _ hW0
  refine ⟨a, ha, fun x z hz => ?_⟩
  have key : ∀ y ∈ t, x - y ∈ scaledInt F κ (b y) → g (x + z) = g x := fun y hy hxy => by
    have hz' : z ∈ scaledInt F κ (b y) := Set.mem_iInter₂.1 (haW hz) y hy
    have h1 : g (y + (x - y)) = g y := hbW y hxy
    have h2 : g (y + (x - y + z)) = g y := hbW y (add_mem hxy hz')
    rw [add_sub_cancel] at h1
    rw [show y + (x - y + z) = x + z by abel] at h2
    rw [h1, h2]
  by_cases hx : x ∈ tsupport g
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact key y hy hxy
  by_cases hxz : x + z ∈ tsupport g
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hxz)
    have hz' : z ∈ scaledInt F κ (b y) := Set.mem_iInter₂.1 (haW hz) y hy
    refine key y hy ?_
    have := sub_mem hxy hz'
    rwa [show x + z - y - z = x - y by abel] at this
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxz]

theorem exists_sum_cosets {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
      g = ∑ r ∈ R, g r • Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) := by
  obtain ⟨a, ha, hinv⟩ := exists_invariant hg
  refine ⟨a, ha, ?_⟩
  set U := scaledInt F κ a
  have hN : ∀ y ∈ tsupport g, {x | x - y ∈ U} ∈ 𝓝 y := fun y _ =>
    ((isOpen_scaledInt a).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover hg.2 _ hN
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ tsupport g, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  refine ⟨R, funext fun x => ?_⟩
  rw [Finset.sum_apply]
  by_cases hx : ∃ r ∈ R, x - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · have h := hinv r0 (x - r0) hxr0
      rw [add_sub_cancel] at h
      simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem (show x ∈ {y | y - r0 ∈ U} from hxr0), mul_one, h]
    · intro r hr hne
      have hm : x ∉ {y | y - r ∈ U} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hm, mul_zero]
  · push Not at hx
    have hK : x ∉ tsupport g := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [image_eq_zero_of_notMem_tsupport hK]
    symm
    refine Finset.sum_eq_zero fun r hr => ?_
    have hm : x ∉ {y | y - r ∈ U} := hx r hr
    simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hm, mul_zero]

theorem exists_sum_finprod {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (φ : Fin m → ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ),
      (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ k, ∀ᶠ v in cofinite, φ k v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      g = ∑ k, c k • fun y => ∏ᶠ v, φ k v fun i => evalV F v (y i) := by
  obtain ⟨a, ha, R, hR⟩ := exists_sum_cosets hg
  choose φ hSB hstd hφ using fun r : κ → FiniteAdeleRing (𝓞 F) F => GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod F κ a r ha
  let e := R.equivFin
  refine ⟨R.card, fun k => g (e.symm k), fun k => φ (e.symm k), fun k v => hSB _ v, fun k => hstd _, ?_⟩
  have hind : ∀ r, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) =
      fun y => ∏ᶠ v, φ r v fun i => evalV F v (y i) := fun r => funext (hφ r)
  refine hR.trans ?_
  simp only [hind]
  rw [← Finset.sum_coe_sort R]
  exact (Equiv.sum_comp e.symm (fun x : R => g x • fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ x v fun i => evalV F v (y i))).symm

theorem comp_mem_adm {κ₁ : Type} [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ₁)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ₁ → Fv F v) → ℂ))
    (hSB : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ₁ → Fv F v))
    (hstd : ∀ᶠ v in cofinite, ev v (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) :
    ∀ l ∈ (adeleClass F).adm κ₁, l ∘ₗ e ∈ (adeleClass F).adm κ := by
  intro l hl g hg
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := exists_sum_finprod hg
  have hψSB : ∀ k v, ev v (φ k v) ∈ GlobalTheory.WeilM.SB (κ₁ → Fv F v) := fun k v => hSB v _ (hφSB k v)
  have hψstd : ∀ k, ∀ᶠ v in cofinite, ev v (φ k v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun k =>
    ((hφstd k).and hstd).mono fun v h => by rw [h.1, h.2]
  have hg' : ∀ k, (fun y : κ₁ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB _ := fun k =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB k) (hψstd k),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB k) (hψstd k)⟩
  choose T hT using fun k => hl _ (hg' k)
  refine ⟨∑ k, c k • (T k).comp ei, fun f => ?_⟩
  have h1 : pureA F (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) g = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  have h2 : ∀ k, e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k)) = pureA F (ei f : (κ₁ → mixedEmbedding.mixedSpace F) → ℂ)
      (fun y => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i)) := fun k =>
    hloc f (φ k) (hφSB k) (hφstd k)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, h1, map_sum, map_smul, h2, hT, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]

end PositivityTheory.ThKF0.Span

end
end

