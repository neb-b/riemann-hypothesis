module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0273
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0292
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnTupleStepZeroReadByMemberLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.AtTrue.StepZeroRead


set_option maxHeartbeats 4000000 in
theorem reads : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ K0 : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), ReadsOne I l Z u a 0 (Nat.zero_le _) (fun _ => ()) K0 ∧ (∀ β, (K0 β).lev.Lb = F.to0.cls0.lev.Lb ∧ (K0 β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ (K0 β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : (K0 β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → (K0 β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, ((K0 ((fun _ : (I.stp u a 0).Cl => ()) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  intro B X I hI hP l Z u Ch0 chOf0 F a Q hQ hF
  obtain ⟨k, hk⟩ := hF.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hk' : I.Reads u I.mu0 0 (fun _ => ()) (fun _ => F.to0.cls0.lev.Lb) (fun _ => F.to0.cls0.lev.U)
      (fun _ => F.to0.cls0.lev.chi) (fun c => (F.to0.cls0.y c).1) (fun c s => (F.to0.cls0.stabI c s).1) (fun _ => k ()) := hk
  choose κ hκ using GlobalTheory.T.memberRepresentative_moved_at_twist_eq_tupleFrames I hI hP l Z u F a Q hQ hF (k ()) hk'
  obtain ⟨K0, hLb, hUloc, hU, hchi, hy, hst⟩ :=
    GlobalTheory.T.stepZeroChart_of_memberLevel I hI hP l Z u a Q F.to0.cls0 κ (fun c s => hk'.stab c s)
  have nQ : ∀ v, ¬ I.UnderQ I.mu0 v := fun v ⟨P, hP', _⟩ => by
    rw [I.twistPrimes_reference_tuple_eq_empty] at hP'
    simp at hP'
  letI := StepZero.idxUnique (hI.idx_ok a)
  refine ⟨K0, ⟨fun _ => k (), ⟨?key, ?onto, ?lb, ?kstd, ?koff, ?kT, ?pt, ?lev, ?chr, ?stab⟩, ?off⟩, ?levs, ?ys⟩
  case key =>
    intro c c'
    exact ⟨fun _ => ⟨Subsingleton.elim _ _, Chart0.cos0 I _ _⟩, fun _ => rfl⟩
  case onto =>
    intro β
    obtain ⟨c0, -⟩ := hk'.onto ()
    exact ⟨I.eCls0 l u a c0, Subsingleton.elim _ _⟩
  case lb =>
    intro β x
    cases β
    rw [hLb]
    exact hk'.lb () x
  case kstd => exact fun _ => hk'.k_std ()
  case koff => exact fun _ v hT _ _ => hk'.k_off () v hT (nQ v) (Or.inl rfl)
  case kT => exact fun _ => hk'.k_T ()
  case pt =>
    intro c
    obtain ⟨c0, rfl⟩ := (I.eCls0 l u a).surjective c
    show PtOf ((show GA B (B.R.N 0) from ((K0 ()).y ⟨I.eCls0 l u a c0, rfl⟩).1) * k ()) _
    rw [hy c0]
    exact (hκ c0).2.2
  case lev =>
    intro c x q hq
    obtain ⟨c0, rfl⟩ := (I.eCls0 l u a).surjective c
    change PtOf ((show GA B (B.R.N 0) from ((K0 ()).y ⟨I.eCls0 l u a c0, rfl⟩).1) * x * k ()) q at hq
    rw [hy c0] at hq
    show x ∈ (K0 ()).lev.U ↔ _
    rw [hU]
    exact GlobalTheory.T.stepZero_level_readAsReference I hI hP l Z u a _ _ _ _ _ (k ()) hk' c0 (κ c0) _ rfl (hκ c0).2.2 x q hq
  case chr =>
    intro c x κ' hg hq
    obtain ⟨c0, rfl⟩ := (I.eCls0 l u a).surjective c
    change PtOf ((show GA B (B.R.N 0) from ((K0 ()).y ⟨I.eCls0 l u a c0, rfl⟩).1) * x.1 * k ()) _ at hq
    rw [hy c0] at hq
    let x' : F.to0.cls0.lev.U := ⟨x.1, hU ▸ x.2⟩
    show (((K0 ()).lev.chi x : ℂˣ) : ℂ) = _
    rw [hchi x x' rfl]
    exact _root_.GlobalTheory.TwU.StepZeroChr.chr_zero I hI hP l Z u a _ _ _ _ _ (k ()) hk' c0 (κ c0) _ rfl (hκ c0).2.2 (hκ c0).2.1 x' κ' hg hq
  case stab => exact fun c s => hst ⟨c, rfl⟩ s
  case off => exact fun _ v hT => hk'.k_off () v hT (nQ v) (Or.inl rfl)
  case levs => exact fun β => by cases β; exact ⟨hLb, hUloc, hU, hchi⟩
  case ys => exact fun c => ⟨κ c, hy c, (hκ c).2.1, (hκ c).1⟩

end GlobalTheory.TwU.AtTrue.StepZeroRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenStringOfAgreement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowValAdd
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.CongSc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def zchar {N : ℕ} [NeZero N] (ζ : ℂˣ) (hζ : ζ ^ N = 1) : Multiplicative (ZMod N) →* ℂˣ where
  toFun x := ζ ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hζ]

theorem zchar_apply {N : ℕ} [NeZero N] (ζ : ℂˣ) (hζ : ζ ^ N = 1) (x : Multiplicative (ZMod N)) :
    zchar ζ hζ x = ζ ^ (Multiplicative.toAdd x).val := rfl

theorem sum_roots {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (k : ℕ) (hk : k < N) :
    ∑ i : Fin N, (ζ ^ (i : ℕ)) ^ k = if k = 0 then (N : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (ζ ^ i) ^ k)]
  simp_rw [← pow_mul, mul_comm _ k, pow_mul]
  split_ifs with h
  · subst h; simp
  · have hne : ζ ^ k ≠ 1 := fun e => h (Nat.eq_zero_of_dvd_of_lt ((hζ.pow_eq_one_iff_dvd k).1 e) hk)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

def stab (W : Wt E n) (f : algForms W) : Subgroup (UA E n) where
  carrier := {x | ∀ v g, f.1 v (g * x) = f.1 v g}
  mul_mem' {x y} hx hy v g := by rw [← mul_assoc, hy, hx]
  one_mem' v g := by rw [mul_one]
  inv_mem' {x} hx v g := by
    have := hx v (g * x⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

theorem stab_level (W : Wt E n) (f : algForms W) (C : Subgroup (UA E n)) (hC : C ≤ finU (E := E) (n := n))
    (hc : IsCompact (C : Set (UA E n))) (ho : ∃ N : Set (UA E n), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU (E := E) (n := n) ⊆ C) :
    IsCompact ((C ⊓ stab W f : Subgroup (UA E n)) : Set (UA E n)) ∧
      ∃ N : Set (UA E n), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU (E := E) (n := n) ⊆ (C ⊓ stab W f : Subgroup (UA E n)) := by
  obtain ⟨N₁, hN₁, h1, hN₁C⟩ := ho
  have hsm := isSmooth_algRep W f
  obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 hsm
  have hfix : ∀ x (hx : x ∈ finU (E := E) (n := n)), x ∈ t → x ∈ stab W f := by
    intro x hx hxt v g
    have : (⟨x, hx⟩ : finU (E := E) (n := n)) ∈ {k : finU (E := E) (n := n) | algRep W k f = f} := by rw [← hte]; exact hxt
    exact congrArg (fun F : algForms W => F.1 v g) this
  have h1t : (1 : UA E n) ∈ t := by
    have : (1 : finU (E := E) (n := n)) ∈ {k : finU (E := E) (n := n) | algRep W k f = f} := by simp
    rw [← hte] at this; exact this
  have hN : N₁ ∩ t ∩ finU (E := E) (n := n) ⊆ (C ⊓ stab W f : Subgroup (UA E n)) := fun x ⟨⟨hx1, hxt⟩, hxf⟩ =>
    ⟨hN₁C ⟨hx1, hxf⟩, hfix x hxf hxt⟩
  refine ⟨?_, N₁ ∩ t, hN₁.inter ht, ⟨h1, h1t⟩, hN⟩
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (((C ⊓ stab W f).subgroupOf C : Subgroup C) : Set C) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      (((hN₁.inter ht).preimage continuous_subtype_val).mem_nhds ⟨h1, h1t⟩) ?_)
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hN ⟨hx, hC x.2⟩)
  have hHc := Subtype.isCompact_iff.1 (Subgroup.isClosed_of_isOpen _ hHo).isCompact
  convert hHc using 1
  ext x; constructor
  · intro hx; exact ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact Subgroup.mem_subgroupOf.1 hy

def opL (s : UA E n →₀ ℂ) : Module.End ℂ (UA E n → ℂ) where
  toFun := opOf (RU E n) s
  map_add' φ ψ := by simp [opOf, Finsupp.sum, Finset.sum_add_distrib, smul_add]
  map_smul' c φ := by simp [opOf, Finsupp.sum, Finset.smul_sum, smul_comm c]

end GlobalTheory.CongSc

namespace GlobalTheory.CongSc

end GlobalTheory.CongSc
end
end

