module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

theorem GStep.Ok.reRep {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} (h : S.Ok)
    (pref : ∀ b, S.D b → Prop) : (S.reRep pref).Ok :=
  ⟨h.fin_orb, h.fin_stab, h.unit, h.root, h.lsh_smul, h.lsh_full_lat, h.stab_inj⟩

theorem GStep.Free.reRep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n} (h : S.Free)
    (pref : ∀ b, S.D b → Prop) : (S.reRep pref).Free := fun b g d hd => h b g d hd

namespace TC

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.xi_unitary (h : I.Ok) (a : I.ι) : (I.xi a).IsUnitary := by
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  exact HChar.isUnitary_of_order hn ((h.xi_reads a).orderDvd hpow)

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.unrepresented_step_conditions (h : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) : (I.stp0 u a i).Ok := by
  have hX : B.fields.Ok := (base_fields_primes_ok B X).1
  have hPr : (B.primes X).Ok := (base_fields_primes_ok B X).2.1
  refine StepOk.stepY_ok _ _ _ _ hX _ _ ?_ ?_ ?_
  · rintro ⟨_ | b, hb⟩ P
    · exact topLev_finiteIndex I.Ch I.sel (I.tup a) (I.cst a) I.Ps i P
    · exact (LevFin.levQ_finiteIndex_and_root I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) hX hPr
        (h.idx_ok a) i (hb.1 rfl) b P).1
  · rintro ⟨_ | b, hb⟩ P g
    · obtain ⟨m, hm, hk⟩ := topLev_root I.Ch I.sel (I.tup a) (I.cst a) I.Ps i P
      exact ⟨m, hm, hk g⟩
    · exact (LevFin.levQ_finiteIndex_and_root I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) hX hPr
        (h.idx_ok a) i (hb.1 rfl) b P).2 g
  · exact fun N hN => (CosetFin.ysAt_finite_nonempty B.R I.sel (I.tup a) (I.cst a) i N hN).1

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.stp_ok (h : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) : (I.stp u a i).Ok := (h.unrepresented_step_conditions u a i).reRep _

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.stp_zero_free (h : I.Ok) (u : B.Word) (a : I.ι) : (I.stp u a 0).Free :=
  GStep.Free.reRep (stepAt_zero_free I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) u (base_fields_primes_ok B X).1
    (base_fields_primes_ok B X).2.1 (base_fields_primes_ok B X).2.2.2.2 (h.idx_ok a).zero_G) _

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.chIn_ok (h : I.Ok) (u : B.Word) (a : I.ι) : (I.chIn u a).Ok := by
  refine
    { step := h.stp_ok u a
      rho_norm := ?_
      rho'_norm := ?_
      DG_pos := DGam_pos (posStar_of_ok (base_fields_primes_ok B X).1) B.R
      dvd_DG := ?_ }
  · intro i _ c
    show ‖((rhoAt I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ)‖ = 1
    exact norm_rhoAt I.SQ I.C (h.xi_unitary a) i _
  · intro i _ c
    show ‖((rhoAt' I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ)‖ = 1
    exact norm_rhoAt' I.SQ I.C (h.xi_unitary a) i _
  · intro i hi c
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have hf := h.stp_zero_free u a
      have : Subsingleton ((I.stp u a 0).Stab c) :=
        ⟨fun x y => Subtype.ext ((hf c.1 x.1 _ x.2).trans (hf c.1 y.1 _ y.2).symm)⟩
      rw [Nat.card_unique]
      exact one_dvd _
    · exact stepY_dvd _ _ _ _ ((I.Tp a).pref u i) (base_fields_primes_ok B X).1 B.R (N_mem_gamRanks B.R hpos hi) c.1 ((I.stp u a i).rep c)

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.idx0 (h : I.Ok) (a : I.ι) : Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) := by
  obtain ⟨b, -⟩ := (h.idx_ok a).zero_uniq
  exact ⟨⟨some b, by simp only [Option.isSome_some, true_iff]; exact lt_of_lt_of_le (by norm_num) B.R.two_le_m⟩⟩

theorem rep_L_lattice (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) :
    Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L :=
  ((I.stp u a i).rep c).1.1.deco.2.L_lattice

theorem ok_chains : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.chIn u a).Ok ∧ Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) ∧ ∀ i c, Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L :=
  fun _ h u a => ⟨h.chIn_ok u a, h.idx0 a, fun i c => rep_L_lattice u a i c⟩

end TC

end GlobalTheory.Mem.Col2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.Crd

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def Ortho (S : Formalism.BasicNotions.HSpace E) : Prop :=
  (∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then 1 else 0) ∧ S.L0 = Submodule.span (𝓞 E) (Set.range S.frame)

theorem ortho_pos (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) : Ortho (Examples₂.posSpace hstar N) :=
  ⟨fun a b => (Examples₂.stdSpace_gram_apply hstar N (fun _ => false) N 0 a b).trans (by simp [Examples₂.sgn]; rfl), rfl⟩

abbrev co (S : Formalism.BasicNotions.HSpace E) {n : ℕ} (h : S.rank = n) : S.V ≃ₗ[E] (Fin n → E) :=
  S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)

theorem Ortho.isStd {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) : Formalism.L2.Herm.IsStd S := ⟨S.frame, h.1, h.2⟩

theorem Ortho.gram {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) {n : ℕ} (hn : S.rank = n) :
    S.gram.reindex (finCongr hn) (finCongr hn) = 1 := by
  subst hn
  ext a b
  simpa [HSpace.gram, Matrix.one_apply] using h.1 a b

theorem Ortho.mem_standardLattice_iff_integral_coords {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) {n : ℕ} (hn : S.rank = n) (x : Fin n → E) :
    x ∈ S.L0.map (((co S hn : S.V ≃ₗ[E] (Fin n → E)) : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ↔
      ∀ j, x j ∈ (algebraMap (𝓞 E) E).range := by
  subst hn
  rw [h.2]
  constructor
  · rintro ⟨v, hv, rfl⟩ j
    have := (Module.Basis.mem_span_iff_repr_mem (𝓞 E) S.frame v).1 hv j
    simpa [co] using this
  · intro hx
    refine ⟨(co S rfl).symm x, (Module.Basis.mem_span_iff_repr_mem (𝓞 E) S.frame _).2 fun j => ?_, (co S rfl).apply_symm_apply x⟩
    have h2 : S.frame.repr ((co S rfl).symm x) j = x j :=
      congrFun ((co S rfl).apply_symm_apply x) j
    rw [h2]
    exact hx j

theorem map_symm_map {S : Formalism.BasicNotions.HSpace E} {n : ℕ} (e : S.V ≃ₗ[E] (Fin n → E)) (L : Submodule (𝓞 E) (Fin n → E)) :
    (L.map ((e.symm : (Fin n → E) →ₗ[E] S.V).restrictScalars (𝓞 E))).map
      ((e : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = L := by
  ext x
  simp

theorem incl_co {S S' : Formalism.BasicNotions.HSpace E} {n : ℕ} (hn : S.rank = n) (hn' : S'.rank = n - 1) (f : S'.V →ₗ[E] S.V)
    (hf : ∀ (a : Fin S'.rank) (b : Fin S.rank), (a : ℕ) = b → f (S'.frame a) = S.frame b) (x : Fin (n - 1) → E) (j : Fin n) :
    co S hn (f ((co S' hn').symm x)) j = if h : j.1 < n - 1 then x ⟨j.1, h⟩ else 0 := by
  subst hn
  have hs : (co S' hn').symm x = ∑ a : Fin (S.rank - 1), x a • S'.frame (finCongr hn'.symm a) := by
    rw [LinearEquiv.symm_apply_eq]
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply, Finset.sum_eq_single k]
    · simp [co]
    · intro a _ ha
      have : ¬ (a : ℕ) = k := fun h => ha (Fin.ext h)
      simp [co, Finsupp.single_apply, Fin.ext_iff, this]
    · simp
  have hb : ∀ a : Fin (S.rank - 1), f (S'.frame (finCongr hn'.symm a)) = S.frame ⟨a.1, by omega⟩ := fun a => hf _ _ rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, map_sum, map_sum]
  simp only [map_smul, hb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hc : ∀ a : Fin (S.rank - 1), co S rfl (S.frame ⟨a.1, by omega⟩) j = if a.1 = j.1 then 1 else 0 := by
    intro a
    simp [co, Fin.ext_iff]
  simp only [hc]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j.1, h⟩]
    · simp
    · intro a _ ha
      rw [if_neg (fun h2 => ha (Fin.ext h2)), mul_zero]
    · simp
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg (fun h2 : a.1 = j.1 => h (h2 ▸ a.2)), mul_zero]

end Gen

end GlobalTheory.Mem.Col2.Crd

end


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mem.Col2.TC.spaces_in_coordinates : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), Formalism.L2.Herm.StdTied (I.rec7 l Z) ∧ gramP (I.rec7 l Z) = 1 ∧ (∀ x j, iXc (I.rec7 l Z) x j = if h : j.1 < B.R.N B.R.m - 1 then x ⟨j.1, h⟩ else 0) ∧ ∀ i (hi : i ≤ B.R.m), gramN (I.rec7 l Z) i hi = 1 ∧ (∀ x, x ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔ ∀ j, x j ∈ (algebraMap (𝓞 B.host.E) B.host.E).range) ∧ ∀ u a, (∀ c, latCrd (I.rec7 l Z) i hi (I.latAt u a i c) = ((I.stp u a i).rep c).1.1.deco.1.L) ∧ ∃ (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY ∧ ∀ τ z, (I.chain l u a).de i z τ = ((eY z).1 τ).det := by
  intro B X I hI hP l Z
  obtain ⟨hs, hX, hX', -⟩ := hI.spaces
  have oX : ∀ j, Crd.Ortho (B.sp.X j) := fun j => by rw [hX]; exact Crd.ortho_pos hs _
  have oX' : Crd.Ortho B.sp.X' := by rw [hX']; exact Crd.ortho_pos hs _
  refine ⟨⟨fun i _ => (oX i).isStd, oX'.isStd⟩, oX'.gram (rankP (I.rec7 l Z)), fun x j => ?_, fun i hi =>
    ⟨(oX i).gram (rankN (I.rec7 l Z) i hi), fun x => (oX i).mem_standardLattice_iff_integral_coords (rankN (I.rec7 l Z) i hi) x, fun u a => ⟨fun c => ?_, ?_⟩⟩⟩
  · exact Crd.incl_co (S := B.sp.X B.R.m) (S' := B.sp.X') (rankN (I.rec7 l Z) _ le_rfl) (rankP (I.rec7 l Z)) B.sp.iX' hP.iX x j
  · unfold TC.latAt
    rw [dite_eq_left hi]
    exact Crd.map_symm_map (S := B.sp.X i) (TC.crd B i hi) _
  · exact ⟨Equiv.refl _, fun _ => rfl, fun _ _ => rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrime
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PerLaw

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem piT_notMem_Q (h : I.Ok) (u : B.Word) (a : I.ι) (P : I.Q a) : (B.primes X).piT u ∉ P.1.asIdeal := fun hm => by
  have hPr := (base_fields_primes_ok B X).2.1
  refine T_notMem_QE I.sel (I.tup a) u hPr h.sel_ok (h.T_mem u) P.1 P.2 ?_
  rw [← hPr.piT_norm u]
  exact P.1.asIdeal.mul_mem_right _ hm

theorem til_deco (h : I.Ok) (u : B.Word) (a : I.ι) (b : (I.perIn u a).S'.β) (p : (I.stX a).D b) :
    ((I.perIn u a).til b p).1.1.deco = DecoSet.tilH (N_m_succ B.R) ((B.primes X).piT u) p.1.1.deco :=
  tilF_deco I.sel (I.tup a) (base_fields_primes_ok B X).2.1 u (piT_notMem_Q h u a) p.1.1

theorem pref_m (u : B.Word) (a : I.ι) (b : (I.stp0 u a B.R.m).β) (q : (I.stp0 u a B.R.m).D b) :
    I.pref u a B.R.m b q ↔ ∃ d, q.1.1 = tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d := by
  have hm := B.R.two_le_m
  rw [← topLev_pref_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps u]
  exact ⟨fun h => h.2.2, fun h => ⟨fun e => by omega, fun e => by omega, h⟩⟩

theorem stX_ok (a : I.ι) : (I.stX a).Ok := by
  have hX := (base_fields_primes_ok B X).1
  let y := Ys.triv B.fields (B.R.N B.R.m - 1)
  let Λ := rowTyG I.Ch I.Ps
  let Θ := levQX B.R I.sel (I.tup a)
  have hRoot (g : Θ.grp) : IsOfFinOrder (Θ.chr g) := by
    rw [show Θ.chr g = ∏ P, (Θ P).lam (piProj (fun P => (Θ P).H) P g) from
      piChar_apply (fun P => (Θ P).H) (fun P => (Θ P).lam) g]
    refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) IsOfFinOrder.one ?_
    intro P _
    obtain ⟨m, hm, hpow⟩ := levQX_root (R := B.R) I.sel (I.tup a) P
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, hpow _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stepY_fin_orb (ST := ∅) y Unit (fun _ => Λ) (fun _ => Θ) (fun _ => True) hX
      (fun _ => levQX_finiteIndex I.sel (I.tup a)) (fun _ _ => Set.finite_singleton _)
  · intro b p
    haveI : Finite (autO p.1.1.deco.1.N) := by
      first
      | exact autO_finite (posStar_of_ok hX) p.1.1.deco.full_lattice
      | exact autO_finite (posStar_of_ok hX) p.1.1.deco.full_lattice.toIsLattice
    exact Finite.of_injective _ (stabAut_inj y Unit (fun _ => Λ) (fun _ => Θ) (fun _ => True) b p)
  · intro _ g
    let M : Matrix (Fin (B.R.N B.R.m - 1)) (Fin (B.R.N B.R.m - 1)) B.fields.E := ↑(toGLm _ _ g.1.1)
    have h : Mᴴ * 1 * M = 1 := toGLm_mem_UJ g.1
    rw [Matrix.mul_one] at h
    exact h
  · intro _ g
    exact isOfFinOrder_iff_pow_eq_one.1
      ((MonoidHom.isOfFinOrder Λ.chr (isOfFinOrder_of_finite g.2.1)).mul (hRoot g.2.2))
  · intro _ g p x
    show (↑(toGLm _ _ g.1.1) : Matrix _ _ _) *ᵥ x ∈ (p.1.1.deco.1.act g.1.1 g.2.1.1).Lsh ↔
      x ∈ p.1.1.deco.1.Lsh
    rw [toGLm_mulVec, Deco.Lsh_act _ g.1.2, mem_gmap, LinearEquiv.symm_apply_apply]
  · intro _ p
    first
    | exact p.1.1.deco.2.Lsh_full_lattice
    | exact p.1.1.deco.2.Lsh_full_lattice.toIsLattice
  · intro b g p h h₁
    exact stepY_eq_one y Unit (fun _ => Λ) (fun _ => Θ) (fun _ => True) b g p h
      (Subtype.ext ((toGLm B.fields.E (B.R.N B.R.m - 1)).injective (h₁.trans (map_one _).symm)))


set_option maxHeartbeats 1600000 in
theorem perIn_ok (h : I.Ok) (u : B.Word) (a : I.ι) : (I.perIn u a).Ok := {
  step := stX_ok a
  til_smul _ g p := Subtype.ext (Prod.ext
    (tilF_extTop I.Ch I.sel (I.tup a) (I.cst a) I.Ps (base_fields_primes_ok B X).2.1 u (piT_notMem_Q h u a) g p.1.1)
    (Set.image_empty _).symm)
  ext_inj _ := extTop_injective I.Ch I.sel (I.tup a) (I.cst a) I.Ps
  gam_ini _ g x := (congrArg (iniH (N_m_succ B.R)) (toGLm_mulVec (extUH (N_m_succ B.R) g.1).1 x)).trans
    ((iniH_extUH _ g.1 x).trans (toGLm_mulVec g.1.1 _).symm)
  gam_last _ g x := (congrFun (toGLm_mulVec (extUH (N_m_succ B.R) g.1).1 x) _).trans (extUH_last _ g.1 x)
  chr_ext _ g := chr_extTop I.Ch I.sel (I.tup a) (I.cst a) I.Ps g
  tz_ne := by
    have hPr := (base_fields_primes_ok B X).2.1
    show star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) ≠ 0
    rw [star_ne_zero]
    intro h
    have h1 : (B.primes X).piT u = 0 := RingOfIntegers.ext h
    have h2 := hPr.piT_norm u
    rw [h1, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  Lsh_til b p x := by
    have hPr := (base_fields_primes_ok B X).2.1
    show x ∈ ((I.perIn u a).til b p).1.1.deco.1.Lsh ↔ _
    rw [til_deco h u a b p]
    exact tilH_Lsh _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u)
      (fun P => decoFin_mem_of_mem_divs P.2) (piT_dvd_of_mem (base_fields_primes_ok B X).1 hPr u) x
  rep_til b p := by
    obtain ⟨d, hd⟩ := (pref_m u a _ _).1 (@pref_prefRep _ _ _ ((I.stp0 u a B.R.m).actD _)
      (I.pref u a B.R.m (idxTop I.sel (I.tup a) (I.idx a))) ((I.perIn u a).til b p) ((pref_m u a _ _).2 ⟨p.1.1, rfl⟩))
    exact ⟨(), trivPt _ _ _ _ _ d, (topPt_val I.sel (I.tup a) (I.cst a) u _).symm.trans
      (congrArg (topPt I.sel (I.tup a) (I.cst a) u) hd)⟩
  H_idx _ := (inferInstance : (⊤ : Subgroup _).FiniteIndex)
  H_rat _ g := ⟨g, Subgroup.mem_top _, rfl⟩ }


set_option maxHeartbeats 1600000 in
theorem perIn_over (h : I.Ok) (u : B.Word) (a : I.ι) : (I.perIn u a).Over (I.atIn u a) := {
  norm_tz := by
    show star (star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E)) *
      star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) = ((B.primes X).T u : B.fields.E)
    rw [star_star]
    have h := congrArg (algebraMap (𝓞 B.fields.E) B.fields.E) ((base_fields_primes_ok B X).2.1.piT_norm u)
    rw [map_mul, map_natCast] at h
    exact h
  N_til b p x := by
    have hPr := (base_fields_primes_ok B X).2.1
    show x ∈ ((I.perIn u a).til b p).1.1.deco.1.N ↔ _
    rw [til_deco h u a b p]
    exact tilH_N _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) x
  f_til b p P x hx := by
    have hPr := (base_fields_primes_ok B X).2.1
    change x ∈ ((I.perIn u a).til b p).1.1.deco.1.N at hx
    show ((I.perIn u a).til b p).1.1.deco.1.f P x = _
    rw [til_deco h u a b p] at hx ⊢
    exact tilH_f _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) P x hx }

theorem perIn_laws : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok →
    ∀ u a, (I.perIn u a).Ok ∧ (I.perIn u a).Over (I.atIn u a) :=
  fun _ h u a => ⟨perIn_ok h u a, perIn_over h u a⟩

end GlobalTheory.Mem.Col2.PerLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderTBijective
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.AtLevel

def underT {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) (P : Pr.vT u) :
    {v : HeightOneSpectrum (𝓞 X.F) // ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal} :=
  ⟨P.1.under (𝓞 X.F), by
    show algebraMap (𝓞 X.F) (𝓞 X.E) _ ∈ P.1.asIdeal
    rw [map_natCast]
    exact T_mem_vT hPr u P⟩

theorem underT_bijective {Z : Dat} (hX : Z.X.Ok) (hPr : Z.Pr.Ok) (u : Z.Pr.Word) : Function.Bijective (underT hPr u) := by
  constructor
  · intro P Q h
    have h1 : P.1.asIdeal.under (𝓞 Z.X.F) = Q.1.asIdeal.under (𝓞 Z.X.F) :=
      congrArg (fun v => v.1.asIdeal) h
    rcases GlobalTheory.CharVal.eq_or_eq_conjP hX (GlobalTheory.CharVal.splitOver_vT hX hPr u Q.2).ne h1 with e | e
    · exact Subtype.ext e
    · refine absurd ?_ (conj_piT_notMem hPr u Q)
      have := decoFin_mem_of_mem_divs P.2
      rw [e, mem_conjP] at this
      exact this
  · rintro ⟨v, hv⟩
    have := v.isMaximal
    obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 Z.X.E) v.asIdeal
    have hT : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∈ Q := by
      rw [hQv.over, Ideal.under_def, Ideal.mem_comap, map_natCast] at hv
      exact hv
    have hne : Q ≠ ⊥ := fun e => by
      rw [e, Ideal.mem_bot] at hT
      exact (hPr.T_prime u).ne_zero (by exact_mod_cast hT)
    let P : HeightOneSpectrum (𝓞 Z.X.E) := ⟨Q, hQ.isPrime, hne⟩
    rw [← hPr.piT_norm u] at hT
    rcases hQ.isPrime.mem_or_mem hT with h | h
    · exact ⟨⟨P, (mem_divs (hPr.piT_ne_zero u) P).2 h⟩, Subtype.ext (HeightOneSpectrum.ext hQv.over.symm)⟩
    · exact ⟨⟨conjPrime₂ P, (mem_divs (hPr.piT_ne_zero u) _).2 ((mem_conjP P _).2 h)⟩,
        Subtype.ext (HeightOneSpectrum.ext ((GlobalTheory.CharVal.under_conjP hX P).trans hQv.over.symm))⟩

theorem seenBar_of_not {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal) (hs : ¬ seenC Pr u w) (τ : X.Tau) :
    X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal := by
  rw [← map_natCast (X.embO τ), ← hPr.piT_norm u, map_mul] at hw
  refine (w.isPrime.mem_or_mem hw).resolve_left fun h => hs fun τ' => ?_
  rw [show X.embO τ' (Pr.piT u) = X.embO τ (Pr.piT u) from RingOfIntegers.ext (hPr.piT_Kq u _ _)]
  exact h

theorem mk_surj {X : Fields} (P : HeightOneSpectrum (𝓞 X.E)) : Function.Surjective (Ideal.Quotient.mk P.asIdeal) :=
  Ideal.Quotient.mk_surjective

theorem mk_zero {X : Fields} (P : HeightOneSpectrum (𝓞 X.E)) (x : 𝓞 X.E) : x ∈ P.asIdeal ↔ Ideal.Quotient.mk P.asIdeal x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.symm


set_option maxHeartbeats 1000000 in
def atTTied {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    AtTTied (D := (I.rec7 l Z)) u where
  eV := Equiv.ofBijective (underT l.pr u)
    (underT_bijective (Z := B.dat X I.Ch) (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1.ok l.pr u)
  piU := X.piT u
  piU_K := X.piT_K u
  piU_norm := X.piT_norm u
  piU_cong := Ideal.mem_span_singleton.2 (X.piT_cong u)
  res := I.resT l u I.mu0
  res_surj v := mk_surj (X := B.fields) v.1
  res_pi v := (mk_zero (X := B.fields) v.1 _).1 (decoFin_mem_of_mem_divs (A := 𝓞 B.fields.E) v.2)
  res_conj v pb h e := by
    have h1 : pb = B.fields.conjO (X.piT u) := RingOfIntegers.ext (h.trans (B.fields_conjO_coe _).symm)
    exact conj_piT_notMem l.pr u v (h1 ▸ Ideal.Quotient.eq_zero_iff_mem.1 e)
  res_v v x := mk_zero (X := B.fields) v.1 _
  tauOf w hw v x := by
    have hval := Formalism.BasicNotions.Examples₂.placesOf_val_eq B.LL
    have hw' : ((B.T u : ℕ) : 𝓞 B.LL) ∈ w.asIdeal :=
      (show B.places.resChar w = B.T u from hw) ▸ resChar_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w
    exact (tauAt_mem_iff l.pr u (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1 hw' v x).symm.trans
      (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).symm
  seenP w hw τ := by
    classical
    have hval := Formalism.BasicNotions.Examples₂.placesOf_val_eq B.LL
    have hw' : ((B.T u : ℕ) : 𝓞 B.LL) ∈ w.asIdeal :=
      (show B.places.resChar w = B.T u from hw) ▸ resChar_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w
    have hs : (((I.rec7 l Z).fm u).seenP w = true) ↔ seenC (B.primes X) u w := decide_eq_true_iff
    by_cases h : seenC (B.primes X) u w
    · rw [if_pos (hs.2 h)]
      exact (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).2 (h τ)
    · rw [if_neg (mt hs.1 h)]
      have h2 := (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).2 (seenBar_of_not l.pr u hw' h τ)
      have h3 : ((B.fields.embO τ (B.fields.conjO (X.piT u)) : 𝓞 B.LL) : B.LL) = B.fields.emb τ (B.host.conj (X.piT u : B.host.E)) :=
        congrArg (B.fields.emb τ) (B.fields_conjO_coe _)
      exact h3 ▸ h2

theorem exists_atTTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ u : B.Word, ∃ A : AtTTied (D := (I.rec7 l Z)) u, I.IdV l u I.mu0 A.eV ∧ A.piU = X.piT u ∧ A.res = I.resT l u I.mu0 :=
  fun I _ _ l Z u => ⟨atTTied I l Z u, fun _ => rfl, rfl, by unfold atTTied; rfl⟩

end GlobalTheory.Mem.AtLevel

end
end

