module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0021
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0017
public import Formalism.LocalToGlobal.CharacterGerms.SubstSubst
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0022
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePHaSpan
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0004

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.BlockMembershipSelfConjCharts
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj

section Gen

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem mem_vars_subG {Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C} {ℓ : Letter T r n}
    (h : ℓ ∈ (subG r tau gm plc Q).vars) : ∃ z, ℓ = lam r tau plc z := by
  unfold subG at h
  rw [MvPolynomial.aeval_eq_bind₁] at h
  obtain ⟨y, _, hy⟩ := MvPolynomial.mem_vars_bind₁ _ _ h
  have h1 := MvPolynomial.vars_sum_subset _ _ hy
  rw [Finset.mem_biUnion] at h1
  obtain ⟨col, _, h2⟩ := h1
  have h3 := MvPolynomial.vars_mul _ _ h2
  rw [MvPolynomial.vars_C, Finset.empty_union, MvPolynomial.vars_X, Finset.mem_singleton] at h3
  exact ⟨((eW r tau N y).1, col), h3⟩

theorem coS_off (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2) (α : AA r tau N) (col : Fin 2)
    (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) (h : y.1 ≠ α.1) :
    coS r tau gm plc (lam r tau plc (α, col)) y = 0 := by
  have e : y = (eW r tau N).symm ((eW r tau N y).1, (eW r tau N y).2) := by
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
  rw [e, coS_lam plc inj, if_neg]
  intro h2
  apply h
  rw [h2]
  rfl

theorem isImgS_subG {dd : ℕ} (X : ∀ o, RawChart C 2 (fun _ => IIs r tau o) (Fin 2 × Fin dd))
    (uv : Letter T r n → Fin dd → C) (e : ∀ o, IIs r tau o → Fin dd → C)
    (hu : ∀ o g (c : IIs r tau o) x, (X o).u g c x = gm o c.1 x.1 g * e o c x.2)
    (huv : ∀ o (c : IIs r tau o) b, uv ⟨tau o c.1, c.2, b⟩ = e o c)
    (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    IsImgS X plc (fun ℓ : Letter T r n => ℓ.2.2) uv (subG r tau gm plc Q) Q := by
  refine ⟨coS r tau gm plc, ?_, (back_subG plc inj gm_hyp Q).symm⟩
  intro ℓ hℓ
  obtain ⟨⟨α, col⟩, rfl⟩ := mem_vars_subG plc hℓ
  refine ⟨α.1, col, rfl, fun ρ' w h => coS_off plc inj α col (ρ', w) h, ?_⟩
  have h1 : (∑ w : (WVO fun o (_ : Fin 2) => IIs r tau o), coS r tau gm plc (lam r tau plc (α, col)) (α.1, w) •
      (X w.1).u w.2.1 w.2.2) =
      ∑ y : Fin N × (WVO fun o (_ : Fin 2) => IIs r tau o), coS r tau gm plc (lam r tau plc (α, col)) y •
        (X y.2.1).u y.2.2.1 y.2.2.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single α.1]
    · intro ρ' _ hne
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [coS_off plc inj α col (ρ', w) hne, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, sum_coS plc inj α col (fun c y => c • (X y.2.1).u y.2.2.1 y.2.2.2) (fun y => zero_smul _ _)]
  funext x
  rw [Finset.sum_apply]
  have h2 : ∀ g, (Mm r tau gm α col g • (X ((eW r tau N).symm (α, g)).2.1).u ((eW r tau N).symm (α, g)).2.2.1
      ((eW r tau N).symm (α, g)).2.2.2) x = (Gm r tau gm α x.1 g * Mm r tau gm α col g) * e α.2.1 α.2.2 x.2 := by
    intro g
    rw [Pi.smul_apply, smul_eq_mul]
    show Mm r tau gm α col g * (X α.2.1).u g α.2.2 x = _
    rw [hu]
    unfold Gm
    ring
  simp only [h2]
  rw [← Finset.sum_mul, gram_matrix_mul_left gm_hyp α col x.1]
  have h3 : uv (lam r tau plc (α, col)) = e α.2.1 α.2.2 := huv α.2.1 α.2.2 _
  rw [h3]
  split_ifs <;> simp

end Gen

theorem BlockMembershipSelfConjugate.mono {C : Type} [Field C] {V : VF C} {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type}
    [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)] {X : ∀ o, RowData C V 2 (I o) (J o)} {n : ℕ} {F : ∀ o, Flag (X o)}
    {FF FF' : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {gaC : Orb → ZMod 2 → ℕ → ℕ}
    (h : BlockMembershipSelfConjugate X n F FF gaC) (hs : FF ⊆ FF') : BlockMembershipSelfConjugate X n F FF' gaC :=
  fun L h1 h2 pl hpl => hs (h L h1 h2 pl hpl)

section Chart

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]

theorem hd_eq_one {ι : T.Fr →+* C} {lab : LabS E C Orb 2} (ha : LabSArith V io ι lab) : lab.hd = 1 := by
  have h := ha.hd_ne
  generalize lab.hd = x at h
  revert x
  decide

theorem gm_mem {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (o : Orb) (t : ZMod 2) (q s : Fin 2) :
    lab.gm o t q s ∈ V.RR := by
  obtain ⟨M, hM⟩ := ha.gm_lim o 0
  have h1 : V.Ge 0 (lab.gm o t q s - emA3 io ι (lab.tau o t) (M q s)) := by simpa using hM t q s
  have h2 := h1.add (hg.em_int o t (M q s))
  rwa [sub_add_cancel] at h2

theorem first_family_subset_image {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (a : (E →+* ℂ) × ℕ → ℕ) {N n : ℕ}
    (plc : Fin N × Fin 2 ↪ Fin n) :
    selfConjTuplesInLattice Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) lab.tau lab.gm V.RR plc ⊆
      imgFamS Y (selfOfLab ha hg) (chartLetterSystem C3 V ι a) n plc := by
  intro Po hPo
  refine ⟨subG Dw.mult lab.tau lab.gm plc (∏ o, toAll o (Po o)), hPo, ?_⟩
  exact isImgS_subG plc (fun o => Y.rawSelf (selfOfLab ha hg o))
    (fun (ℓ : LtN Dw n) i => ι (chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩ i)) (fun o => selfLieBasisVector C3 ι lab o) (fun _ _ _ _ => rfl)
    (fun _ _ _ => rfl) ha.inj (fun o t s s' => by have := ha.gm_hyp o t s s'; rwa [hd_eq_one ha] at this) _

theorem block_membership_self_conj_charts (h1 : IsotropicToStdSubstHarmonic) (h2 : IsotropicToStdSubstLineInvariant) (h3 : IsotropicToStdSubstLineDegree)
    {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (Hy : ∀ o, (Y.rawSelf (selfOfLab ha hg o)).Hyps V)
    (a : (E →+* ℂ) × ℕ → ℕ) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
    (F : ∀ o, Flag (rdS Y (selfOfLab ha hg) Hy o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)
    (std : ∀ o g t (q : Fin ((rdS Y (selfOfLab ha hg) Hy o).rkF g t)), ((F o).en g t q).2.val = q.val)
    (alt : ∀ o, (rdS Y (selfOfLab ha hg) Hy o).Alt) (hj : lab.j' < lab.n)
    (supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s)
    (tie : WtTieC Dw.mult lab.tau gaC fun τ i => a (τ, i)) :
    BlockMembershipSelfConjugate (fun o => rdS Y (selfOfLab ha hg) Hy o) N F (imgFamS Y (selfOfLab ha hg) (chartLetterSystem C3 V ι a) n plc) gaC :=
  (block_membership_self_conj_first Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) lab.tau lab.gm V.RR plc h1 h2 h3 first_chern_integral
    (fun o => rdS Y (selfOfLab ha hg) Hy o) F gaC ha.inj (fun o t => by rw [ha.conj o t, hd_eq_one ha])
    (fun o t s s' => by have := ha.gm_hyp o t s s'; rwa [hd_eq_one ha] at this) (gm_mem ha hg)
    (fun o g x => by
      show (if g = 0 then x.1 else x.1 + lab.hd) = _
      rw [hd_eq_one ha])
    std alt (fun _ => hj) supp tie).mono (first_family_subset_image ha hg a plc)

end Chart

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffSinglePointZero
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

section Pull

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem cc_X {σ : Type} (s : σ) : MvPowerSeries.constantCoeff (MvPowerSeries.X s : MvPowerSeries σ C) = 0 := MvPowerSeries.constantCoeff_X s

end Pull

section Emb

variable {n : ℕ}

def eRow (b : Fin n) : WVO I ↪ Fin n × WVO I := ⟨fun w => (b, w), Prod.mk_right_injective b⟩

def eAll (n : ℕ) (o : Orb) : Fin n × WV (I o) ↪ Fin n × WVO I :=
  ⟨fun x => (x.1, (⟨o, x.2⟩ : WVO I)), fun x y h => by
    have h1 : x.1 = y.1 := (Prod.ext_iff.1 h).1
    have h2 : (⟨o, x.2⟩ : WVO I) = ⟨o, y.2⟩ := (Prod.ext_iff.1 h).2
    exact Prod.ext h1 (eq_of_heq (Sigma.mk.inj h2).2)⟩

theorem rowOf_eq (b : Fin n) (F : MvPowerSeries (WVO I) C) : rowOf b F = MvPowerSeries.rename (eRow b) F := by
  unfold rowOf
  rw [MvPowerSeries.rename_eq_subst]
  rfl

theorem rowOf_toAllS (b : Fin n) (o : Orb) (F : MvPowerSeries (WV (I o)) C) :
    rowOf b (toAllS o F) = MvPowerSeries.rename (eAll n o) (rowCopy b F) := by
  have e1 : toAllS o F =
      MvPowerSeries.rename (Function.Embedding.sigmaMk (β := fun o => WV (I o)) o) F := by
    unfold toAllS
    rw [MvPowerSeries.rename_eq_subst]
    rfl
  rw [rowOf_eq, e1, rtj_rowCopy_eq, MvPowerSeries.rename_rename, MvPowerSeries.rename_rename]
  exact rtj_rename_congr (by funext w; rfl) F

theorem rowOf_mul (b : Fin n) (F G : MvPowerSeries (WVO I) C) : rowOf b (F * G) = rowOf b F * rowOf b G := by
  unfold rowOf
  exact VP.subst_mul (fun _ => MvPowerSeries.constantCoeff_X _) F G

theorem rowOf_prod (b : Fin n) {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries (WVO I) C) :
    rowOf b (∏ i ∈ s, F i) = ∏ i ∈ s, rowOf b (F i) := by
  unfold rowOf
  exact VP.subst_prod (fun _ => MvPowerSeries.constantCoeff_X _) s F

theorem toAllS_mul (o : Orb) (F G : MvPowerSeries (WV (I o)) C) : toAllS o (F * G) = toAllS o F * toAllS o G := by
  unfold toAllS
  exact VP.subst_mul (fun _ => MvPowerSeries.constantCoeff_X _) F G

theorem jet_orb (Po : ∀ o, MvPolynomial (Fin n × WV (I o)) C) (Φ : ∀ o, MvPowerSeries (Fin n × WV (I o)) C) :
    jetAt0 (∏ o, toAll o (Po o)) (∏ o, MvPowerSeries.rename (eAll n o) (Φ o)) = ∏ o, jetAt0 (Po o) (Φ o) := by
  have hA : ∀ o ∈ (Finset.univ : Finset Orb), ∀ o' ∈ (Finset.univ : Finset Orb), o ≠ o' →
      Disjoint (Set.range (eAll (I := I) n o)) (Set.range (eAll (I := I) n o')) := by
    intro o _ o' _ h
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    exact h (congrArg (fun z : Fin n × WVO I => z.2.1) hy).symm
  have hT : ∀ o, toAll o (Po o) = MvPolynomial.rename (eAll n o) (Po o) := fun o => rfl
  exact (rtj_jet_prod (fun o => Set.range (eAll (I := I) n o)) Finset.univ hA
    (fun o => toAll o (Po o)) (fun o => MvPowerSeries.rename (eAll n o) (Φ o))
    (fun o _ => by rw [hT]; exact rtj_rename_supported _ _)
    (fun o _ => rtj_serIn_rename _ _)).trans
    (Finset.prod_congr rfl fun o _ => by rw [hT]; exact rtj_jet_rename _ _ _)

end Emb

end VP

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.FrobPowSmul
section
noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem frobPow_smul : ∀ (C : Type) [Field C] (V : VF C) (σ : Type) (f : MvPowerSeries σ C), IntS V f →
    ∀ μ : σ →₀ ℕ, V.MM (MvPowerSeries.coeff (V.l • μ) (f ^ V.l) - MvPowerSeries.coeff μ f ^ V.l) := by
  intro C _ V σ f hf μ
  have hl : 0 < V.l := V.l_prime.pos
  have h := PhPowP.frobPowMv f hf (V.l • μ)
  have hdiv : ∀ t, V.l ∣ (V.l • μ) t := fun t => by simp [Finsupp.smul_apply]
  have hdl : PhPowP.divL V.l (V.l • μ) = μ := by
    ext t
    rw [PhPowP.divL_apply, Finsupp.smul_apply, smul_eq_mul, Nat.mul_div_cancel_left _ hl]
  rw [if_pos hdiv, hdl] at h
  exact h

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.IsWHLetterMinorK
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

namespace WeightHomogeneousLetters

open WeightHomogeneousMinors

section WH

variable {R : Type} [CommRing R]

theorem isWH_aeval {σ τ : Type} {w : τ → ℕ} {w' : σ → ℕ} (f : σ → MvPolynomial τ R)
    (hf : ∀ x, IsWeightedHomogeneous w (f x) (w' x)) {p : MvPolynomial σ R} {D : ℕ}
    (hp : IsWeightedHomogeneous w' p D) : IsWeightedHomogeneous w (aeval f p) D := by
  rw [aeval_def, eval₂_eq]
  apply IsWeightedHomogeneous.sum
  intro m hm
  have h1 : IsWeightedHomogeneous w (∏ i ∈ m.support, f i ^ m i) (∑ i ∈ m.support, m i • w' i) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => (hf i).pow (m i)
  have h2 : (∑ i ∈ m.support, m i • w' i) = D := by
    rw [← hp (mem_support_iff.1 hm), Finsupp.weight_apply]
    rfl
  have h3 := (isWeightedHomogeneous_C w (AddMonoidAlgebra.coeff p m)).mul h1
  rw [zero_add, h2] at h3
  exact h3

theorem isWH_add {σ : Type} {w1 w2 : σ → ℕ} {p : MvPolynomial σ R} {D1 D2 : ℕ}
    (h1 : IsWeightedHomogeneous w1 p D1) (h2 : IsWeightedHomogeneous w2 p D2) :
    IsWeightedHomogeneous (fun x => w1 x + w2 x) p (D1 + D2) := by
  intro m hm
  have e1 := h1 hm
  have e2 := h2 hm
  simp only [Finsupp.weight_apply, Finsupp.sum] at e1 e2 ⊢
  rw [← e1, ← e2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => smul_add _ _ _

end WH

section Block

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X) (idx : ∀ g, I g → ℕ) (std : ∀ g t (c : Fin (X.rkF g t)), idx g (F.en g t c) = c.val)

def wRowG {N : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (x : Fin N × WV I) : ℕ :=
  if x.2.1 = g0 ∧ (X.G x.2.1).ty (Sum.inl x.2.2) = t0 ∧ idx x.2.1 x.2.2 = c0 then 1 else 0

include std in
theorem wRowG_letter {N : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d)
    (x : Fin N × Fin (X.rkF g t)) :
    wRowG X idx g0 t0 c0 (F.letter g t x) = if (g = g0 ∧ t = t0) ∧ (x.2 : ℕ) = c0 then 1 else 0 := by
  simp only [wRowG, Flag.letter, F.en_ty, std, and_assoc]

include std in
theorem isWH_letter_minorK {N k : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) :
    IsWeightedHomogeneous (wRowG X idx (N := N) g0 t0 c0) (rename (F.letter g t) (minorK C N (X.rkF g t) k))
      (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0) :=
  isWH_rename _ (isWH_minorK_row (g = g0 ∧ t = t0) c0 fun x => wRowG_letter X F idx std g0 t0 c0 g t x)

theorem num_ch (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) (u : ℕ) :
    u • (if X.n ≤ X.n ∧ X.n ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < X.n then 1 else 0) =
      ∑ k ∈ Finset.Icc (c0 + 1) (X.rkF g0 t0), (if g0 = g ∧ t0 = t ∧ k = X.n then u else 0) := by
  by_cases hg : g = g0 ∧ t = t0
  · obtain ⟨rfl, rfl⟩ := hg
    simp only [le_refl, true_and, and_true, Finset.sum_ite_eq', Finset.mem_Icc]
    split_ifs <;> first | omega | simp
  · rw [if_neg (fun h => hg h.2.2.1), smul_zero, Finset.sum_eq_zero]
    intro k _
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hg ⟨h1.symm, h2.symm⟩

theorem num_mon (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) :
    (∑ t : ZMod d, ∑ k ∈ Finset.Icc 1 (min N (X.rkF g t)),
      e t k • (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0)) =
      ∑ k ∈ Finset.Icc (c0 + 1) (X.rkF g0 t0),
        (if g0 = g ∧ 1 ≤ k ∧ k ≤ min N (X.rkF g t0) then e t0 k else 0) := by
  by_cases hg : g0 = g
  · subst hg
    rw [Fintype.sum_eq_single t0]
    · simp only [eq_self_iff_true, true_and, and_true, smul_ite, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    · intro t ht
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg (fun h => ht h.2.2.1.2), smul_zero]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    all_goals first
      | (intro k _; rw [if_neg (fun h => hg h.1)])
      | (intro t _; exact Finset.sum_eq_zero fun k _ => by rw [if_neg (fun h => hg h.2.2.1.1.symm), smul_zero])


include std in
theorem blockPoly_isWeightedHomogeneous' (b : GlobalTheory d) (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) :
    IsWeightedHomogeneous (wRowG X idx g0 t0 c0) (b.poly X F)
      (∑ k ∈ Finset.Icc (c0 + 1) (X.rkF g0 t0), b.wt X g0 t0 k) := by
  cases b with
  | ch g t u =>
    exact isWH_deg ((isWH_letter_minorK X F idx std g0 t0 c0 g t).pow u) (num_ch X g0 t0 c0 g t u)
  | bi g t i y =>
    refine isWH_deg (((isWH_letter_minorK X F idx std g0 t0 c0 g t).pow (V.l ^ i * y)).mul
      ((isWH_letter_minorK X F idx std g0 t0 c0 (1 - g) (t + (i : ZMod d))).pow y)) ?_
    simp only [GlobalTheory.wt]
    rw [Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) (num_ch X g0 t0 c0 g t _) (num_ch X g0 t0 c0 (1 - g) (t + (i : ZMod d)) y)
  | mon g e N =>
    refine isWH_deg (IsWeightedHomogeneous.prod _ _ _ fun t _ => isWH_rename _
      (IsWeightedHomogeneous.prod _ _ _ fun k _ =>
        (isWH_minorK_row (g = g0 ∧ t = t0) c0 fun x => wRowG_letter X F idx std g0 t0 c0 g t x).pow (e t k))) ?_
    simp only [GlobalTheory.wt]
    exact num_mon X g0 t0 c0 g e N

end Block

end WeightHomogeneousLetters

end Formalism.L2.FormalSeriesBounds.RF
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RankMaximalOfNondegenerateOfUnitSeriesIntegral
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Defs

variable {C : Type} [Field C]

def mulL {dd : ℕ} (F : Fin dd → PS C 2 dd) : ℕ → Pt C 1 dd
  | 0 => fun _ => 0
  | n + 1 => addOf F (mulL F n) (pt C dd 0)

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.u1 (Y : FBChart C V O dd) : PS C 2 dd :=
  FB.expS C (ev (n := 2) ![comp1 (mulL Y.B.G.F V.l) (pt C (n := 2) dd 0), pt C dd 1] Y.h - (V.l : C) • Y.h)

def FBChart.aOf (Y : FBChart C V O dd) (u : Fin dd → C) : PS C 1 dd :=
  fun ν => ∑ i, u i ^ V.l * MvPowerSeries.coeff
    (Finsupp.single ((0 : Fin 2), i) V.l + ν.mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1

end Defs

def FirstUnitSeriesIntegral : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd), IntS V Y.u1

def FirstUnitSeriesFrobenius : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (μ : Fin 2 × Fin dd →₀ ℕ), (∃ i, ¬ V.l ∣ μ ((0 : Fin 2), i)) →
      V.MM (MvPowerSeries.coeff μ Y.u1)

def MulLFrobSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (k : Fin dd) (μ : Fin 1 × Fin dd →₀ ℕ), (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) →
      V.MM (MvPowerSeries.coeff μ (mulL Y.B.G.F V.l k))

theorem intS_aOf {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (h : IntS V Y.u1) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) : IntS V (Y.aOf u) := by
  intro ν
  show V.Ge 0 (∑ i, u i ^ V.l * MvPowerSeries.coeff
    (Finsupp.single ((0 : Fin 2), i) V.l + ν.mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1)
  exact VF.Ge.sum fun i _ => by simpa using ((hu i).pow V.l).mul (h _)

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieGermI
section
namespace Formalism.L2.FormalSeriesBounds

theorem germIAll_holds : GermIAllSt := fun _ _ _ _ _ _ _ _ Y => germI_holds Y

end Formalism.L2.FormalSeriesBounds
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePDescSpanFinal
section
set_option autoImplicit false

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem descent_span : DescSpanSt Xo c :=
  descSpanSt_of (HaP.haSpanSt_of HaP.satRetr HaP.rowInvUp)

end Formalism.L2.FormalSeriesBounds
end

