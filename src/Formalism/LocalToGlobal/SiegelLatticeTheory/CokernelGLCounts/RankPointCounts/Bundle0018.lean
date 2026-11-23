module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportProposition

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CellRelIff
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

def Ak : Subgroup K := S.subgroupOf K

def πk (hD : Data W S N' K π) : K →* Ak S K where
  toFun k := ⟨⟨π k, hD.kπ k k.2⟩, by show π k ∈ S; exact hD.mem k⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

theorem πk_id (hD : Data W S N' K π) (a : Ak S K) : πk W S N' K π hD a = a := by
  obtain ⟨⟨x, hxK⟩, hxS⟩ := a
  have hxS' : x ∈ S := by simpa [Ak, Subgroup.mem_subgroupOf] using hxS
  ext
  simp [πk, hD.id x hxS']

def Hk : Subgroup K := (Hs W K g).subgroupOf K

theorem cellRel_iff (hD : Data W S N' K π) (k₁ k₂ : K) :
    (cellRel W N' K g).r (toCell W S N' K π g hD k₁) (toCell W S N' K π g hD k₂) ↔
      ∃ n ∈ (πk W S N' K π hD).ker, ∃ h ∈ Hk W K g, k₂ = n * k₁ * h := by
  show cell π ((k₂ : G) * g) * (cell π ((k₁ : G) * g))⁻¹ ∈ K ⊓ N' ↔ _
  constructor
  · rintro ⟨hK, hN⟩
    set x := cell π ((k₂ : G) * g) * (cell π ((k₁ : G) * g))⁻¹ with hx
    refine ⟨⟨x, hK⟩, ?_, k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂, ?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      have h1 : π x = 1 := (hD.ker x).1 hN
      ext
      simp [πk, h1]
    · rw [Hk, Subgroup.mem_subgroupOf, Hs, Subgroup.mem_inf]
      refine ⟨(k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂).2, ?_⟩
      rw [MulAction.mem_stabilizer_iff]
      have e2 := cell_smul W S N' K π hD ((k₂ : G) * g)
      have e1 := cell_smul W S N' K π hD ((k₁ : G) * g)
      calc ((k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂ : K) : G) • g • W
          = ((k₁ : G)⁻¹ * cell π ((k₁ : G) * g)) • ((cell π ((k₂ : G) * g))⁻¹ • (((k₂ : G) * g) • W)) := by
            rw [← mul_smul, ← mul_smul, ← mul_smul]
            congr 1
            push_cast
            rw [hx]
            group
        _ = ((k₁ : G)⁻¹ * cell π ((k₁ : G) * g)) • W := by rw [← e2, inv_smul_smul]
        _ = g • W := by rw [mul_smul, e1, ← mul_smul]; simp
    · ext
      push_cast
      group
  · rintro ⟨n, hn, h, hh, rfl⟩
    have hπn : π (n : G) = 1 := by
      rw [MonoidHom.mem_ker] at hn
      have := congrArg (fun a : Ak S K => ((a : K) : G)) hn
      simpa [πk] using this
    have hh' : (h : G) • g • W = g • W := by
      rw [Hk, Subgroup.mem_subgroupOf, Hs, Subgroup.mem_inf] at hh
      exact hh.2
    have hs : g⁻¹ * (h : G) * g ∈ S := by
      rw [← hD.stab]
      rw [mul_smul, mul_smul, hh', ← mul_smul]
      simp
    have key : cell π (((n * k₁ * h : K) : G) * g) = (n : G) * cell π ((k₁ : G) * g) := by
      have e : ((n * k₁ * h : K) : G) * g = (n : G) * ((k₁ : G) * g) * (g⁻¹ * (h : G) * g) := by
        push_cast
        group
      simp only [cell]
      rw [e, map_mul, map_mul, hπn, hD.id _ hs]
      group
    rw [key, mul_inv_cancel_right]
    exact ⟨n.2, (hD.ker n).2 hπn⟩

end Formalism.L2.SG.Pf.CountAb
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Chi2ApplyOne
section
noncomputable section

namespace Formalism.L2.SG.IntegralApproximation

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped Classical TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Vol

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def FiniteLevelVolumeEquality : Prop := (X.measG.μGf (levelUnitary X hb)).toReal = (X.B.μf X.K2).toReal

def CovolTie : Prop :=
  covolBy (G := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) X.measG.μG =
    X.B.I.vol X.B.μf X.B.fund

theorem chi2_apply_one (hK : X.LevelSubgroupCharacter) : X.chi2 1 = 1 := by
  obtain ⟨h1, -, -, hmul, hnorm⟩ := hK
  have hm := hmul 1 h1 1 h1
  simp only [mul_one] at hm
  have hne : X.chi2 1 ≠ 0 := by
    intro h0
    have hn := hnorm 1 h1
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  exact mul_left_cancel₀ hne (hm.symm.trans (mul_one _).symm)

theorem e_one_re (hK : X.LevelSubgroupCharacter) : (X.B.e 1).re = ((X.B.μf X.K2).toReal)⁻¹ := by
  have h := X.e_eq 1
  have h1 : (1 : X.B.I.Gf) ∈ X.K2 := hK.1
  change X.B.e 1 = if (1 : X.B.I.Gf) ∈ X.K2 then star (X.chi2 1) / ((X.B.μf X.K2).toReal : ℂ) else 0 at h
  rw [if_pos h1, chi2_apply_one X hK, star_one] at h
  rw [h, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]

end Vol

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem MassDataDstarX (L : LocIn (TypX X)) (A : AnIn) (hH : HypX X hb FdN FdN' u u')
    (hKpp : KppVolAt X hb hK FdN FdN' u u' X0 L A) (h2 : FiniteLevelVolumeEquality X hb) (h3 : CovolTie X) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Dstar = Formalism.L2.SG.RowsConc.DstC X := by
  unfold Formalism.FourierDecayAlt.S3.MassData.Dstar Formalism.L2.SG.RowsConc.DstC Formalism.MainNotions.S.AutInst.Dstar
  rw [e_one_re X hK]
  have hdeg : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).deg =
      Formalism.MainNotions.PlaceDegreeData.fdegAll X.B.I X.B.σ X.B.w := rfl
  have hvol : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG =
      covolBy (G := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) X.measG.μG := rfl
  have hkpp : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKpp =
      (bOf X hb hK FdN FdN' u u' X0 L A).μKpp := rfl
  rw [hdeg, hvol, h3, hkpp, hKpp hH, h2]
  ring

end Formalism.L2.SG.IntegralApproximation
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KappaOffDiagonal
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}

def frq (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) :=
  mapLF q.1.2 (lf D (X.Fu u'))

def fixedSubspaceOfRepresentative (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : Submodule D.host.E (VS D).V :=
  (lf D (X.Fu u)).fl.Xplus ⊔ (frq X q).fl.Xplus

def pointwiseStabilizerInfinite (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : Set X.B.I.Ginf :=
  Hset X.B.I (X.crd '' (fixedSubspaceOfRepresentative X q : Set (VS D).V))

end Defs

def RelRepC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    t.relevant → t.G = 0 →
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X t.rep).fl ∧ Gval (lf D (X.Fu u)) (frq X t.rep) = 0

def CovRepC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl →
    ∀ Ω : Set X.B.I.Ginf, IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' q.1.2) Ω →
    OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') q.1.1.1 →
    ∀ h ∈ pointwiseStabilizerInfinite X q,
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
       (X.piU u h).comp (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') q.1.1.1) =
        (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') q.1.1.1).comp
          (X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1)))

def SchurNFC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    (∀ τ, uS D u τ ≠ uS D u' τ) →
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl → Gval (lf D (X.Fu u)) (frq X q) = 0 →
    ∀ P : X.Vpi u' →L[ℂ] X.Vpi u,
      (∀ h ∈ pointwiseStabilizerInfinite X q, (X.piU u h).comp P = P.comp (X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1))) → P = 0

section Asm

variable {D : D7} {X : HidaSetting D}

theorem words_differ {large₂ : SizeData₂ D} {C' Cl Cg cb Cw cT CT C0 : ℝ}
    (h : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0) {u u' : D.what₂.Word} (huu : u ≠ u') :
    ∀ τ, uS D u τ ≠ uS D u' τ := by
  exact h.1.2.1.2.2.2.2.2.2.2.1 u u' huu

theorem aTerm_eq_zero_of_OOt {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)
    (t : GTerm X u u' F0 F0' what₂ rows') (h : OOt t = 0) : aTerm cs cs' FdN FdN' t = 0 := by
  have hb : ∀ ρ ρ', blk cs cs' FdN FdN' t ρ ρ' = 0 := by
    intro ρ ρ'
    simp [blk, h]
  ext φ : 1
  simp [aTerm, aTermL, hb]
  try rfl

theorem fundOf_spec {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hF : FundExists X u u' F0 F0' what₂ rows') (t : GTerm X u u' F0 F0' what₂ rows') :
    IsSFund X.B.I (ROinf t) (FundOf t) := by
  unfold FundOf
  split_ifs with h0
  · exact h0.choose_spec
  · exact absurd (hF t) h0

end Asm

end Formalism.L2.SG.KappaOffDiagonal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumB
section
noncomputable section

namespace Formalism.L2.SG.LsDatumB

open scoped BigOperators
open Classical

section Abstract

theorem hasSum_of_fiber {P G : Type*} [Finite P] (c : P → ℂ) (cls : P → G) (F : G → ℂ)
    (hF : ∀ g, HasSum (fun x : {x : P // cls x = g} => c x.1) (F g)) {s : ℂ} (hs : HasSum F s) :
    HasSum c s := by
  haveI := Fintype.ofFinite P
  have h1 : HasSum c (∑ x, c x) := hasSum_fintype c
  have h2 := h1.tsum_fiberwise cls
  have e : F = fun g => ∑' x : ↑(cls ⁻¹' {g}), c x := funext fun g => ((hF g).tsum_eq).symm
  have h4 : HasSum F (∑ x, c x) := by
    rw [e]
    exact h2
  rw [hs.unique h4]
  exact h1

variable {ι : Type*} {X : ι → Type*}

def Rst (x0 : ∀ p, X p) : Type _ := {x : ∀ p, X p // {p | x p ≠ x0 p}.Finite}

theorem hasSum_rst (x0 : ∀ p, X p) (f : ∀ p, X p → ℂ) (a : ι → ℂ) (S : Finset ι)
    (hoff : ∀ p ∉ S, ∀ x, f p x = if x = x0 p then 1 else 0)
    (hf : ∀ p ∈ S, HasSum (f p) (a p)) (hn : ∀ p ∈ S, Summable fun x => ‖f p x‖) :
    HasSum (fun x : Rst x0 => ∏ᶠ p, f p (x.1 p)) (∏ p ∈ S, a p) := by
  have h0 := (Formalism.L2.SG.Pf.hasSum_prod_offS x0 f a S hf hn).1
  let j : Formalism.L2.SG.Pf.OffS x0 S → Rst x0 := fun θ =>
    ⟨θ.1, (S.finite_toSet).subset fun p hp => by
      by_contra h
      exact hp (θ.2 p h)⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (congrArg (fun x : Rst x0 => x.1) h)
  have hsupp : ∀ x : Rst x0, (Function.mulSupport fun p => f p (x.1 p)) ⊆ (S : Set ι) ∪ {p | x.1 p ≠ x0 p} := by
    intro x p hp
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hc
    exact (Function.mem_mulSupport.1 hp) (by rw [hoff p hc.1, if_pos hc.2])
  have hfin : ∀ x : Rst x0, (Function.mulSupport fun p => f p (x.1 p)).Finite := fun x =>
    ((S.finite_toSet).union x.2).subset (hsupp x)
  have hzero : ∀ x ∉ Set.range j, (∏ᶠ p, f p (x.1 p)) = 0 := by
    intro x hx
    have : ∃ p ∉ S, x.1 p ≠ x0 p := by
      by_contra h
      push_neg at h
      exact hx ⟨⟨x.1, h⟩, rfl⟩
    obtain ⟨p, hpS, hp⟩ := this
    exact finprod_eq_zero _ p (by rw [hoff p hpS, if_neg hp]) (hfin x)
  rw [← hj.hasSum_iff hzero]
  convert h0 using 1
  funext θ
  apply finprod_eq_prod_of_mulSupport_subset
  intro p hp
  by_contra hS
  exact (Function.mem_mulSupport.1 hp) (by rw [hoff p hS, if_pos (θ.2 p hS)])

theorem hasSum_passage {P G : Type*} [Finite P] (c : P → ℂ) (cls : P → G) (F : G → ℂ)
    (hF : ∀ g, HasSum (fun x : {x : P // cls x = g} => c x.1) (F g))
    (x0 : ∀ p, X p) (loc : G ≃ Rst x0) (f : ∀ p, X p → ℂ) (a : ι → ℂ) (S : Finset ι)
    (hFp : ∀ g, F g = ∏ᶠ p, f p ((loc g).1 p))
    (hoff : ∀ p ∉ S, ∀ x, f p x = if x = x0 p then 1 else 0)
    (hf : ∀ p ∈ S, HasSum (f p) (a p)) (hn : ∀ p ∈ S, Summable fun x => ‖f p x‖) :
    HasSum c (∏ p ∈ S, a p) := by
  have h1 := hasSum_rst x0 f a S hoff hf hn
  have h2 : HasSum F (∏ p ∈ S, a p) := by
    have e : F = (fun x : Rst x0 => ∏ᶠ p, f p (x.1 p)) ∘ loc := funext fun g => hFp g
    rw [e]
    exact (loc.hasSum_iff).2 h1
  exact hasSum_of_fiber c cls F hF h2

end Abstract

end Formalism.L2.SG.LsDatumB
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MmIntOfGeneric
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section G3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def GlueFwd (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∀ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' →
    ∃ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩, IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ ∧
      ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂

def GlueBack (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) → MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ →
    ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩, IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ →
    ∃ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' ∧
      ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂

def GlueInj (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∀ Λ₂ Λ₂' : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' → H.IsGeneric ⟨Λ₂', f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂' φ φ' →
      (∀ m₁ m₂, GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂ ↔
        GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂' φ φ' m₁ m₂) → Λ₂ = Λ₂'

theorem mmInt_of_generic {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (Λ₂ : Submodule M.L.O V) (f₂ f₂' : Fin (r + 1) → V) (T T' : F)
    (hg : H.IsGeneric ⟨Λ₂, f₂, f₂', T, T'⟩) : MMInt H (⟨⊥, f₂, f₂', T, T'⟩ : Term V M r) := by
  have hsub : MMo H (⟨⊥, f₂, f₂', T, T'⟩ : Term V M r) ≤ Λ₂ := by
    refine (Submodule.span_le (R := M.L.O)).2 ?_
    rintro _ ⟨a, rfl⟩
    exact hg.2.1 a
  intro m hm m' hm'
  exact (hg.1.1.2.2 m).1 (hsub hm) m' (hsub hm')

theorem dd_ext {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    {t₁ t₂ : Term V M r} (θ θ' : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂)
    (h : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ ↔ θ' (ddMk H t₁ m₁) = ddMk H t₂ m₂) : θ = θ' := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨m₁, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m₂, hm₂⟩ := Submodule.Quotient.mk_surjective _ (θ (Submodule.Quotient.mk m₁))
  have h₁ : θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ := hm₂.symm
  exact h₁.trans ((h m₁ m₂).1 h₁).symm

theorem glue_of (M : Model F E) (r n : ℕ) (hF : GlueFwd M r n) (hB : GlueBack M r n) (hI : GlueInj M r n) :
    Glue M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp
  have fw := hF V H hn t₁ f₂ f₂' φ φ' hyp
  have bk := hB V H hn t₁ f₂ f₂' φ φ' hyp
  have inj := hI V H hn t₁ f₂ f₂' φ φ' hyp
  let toθ : {Λ₂ : Submodule M.L.O V // H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ'} →
      {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ //
        IsUnit (H.Dl f₂ f₂' (r + 1)) ∧ MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ ∧
          IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ} :=
    fun x => ⟨(fw x.1 x.2.1 x.2.2).choose, x.2.1.1.2.2.2.1, mmInt_of_generic H x.1 f₂ f₂' t₁.T t₁.T' x.2.1,
      (fw x.1 x.2.1 x.2.2).choose_spec.1⟩
  have toθ_spec : ∀ x m₁ m₂, (toθ x).1 (ddMk H t₁ m₁) = ddMk H _ m₂ ↔
      GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ x.1 φ φ' m₁ m₂ :=
    fun x => (fw x.1 x.2.1 x.2.2).choose_spec.2
  have hinj : Function.Injective toθ := by
    intro x y hxy
    apply Subtype.ext
    refine inj x.1 y.1 x.2.1 x.2.2 y.2.1 y.2.2 fun m₁ m₂ => ?_
    rw [← toθ_spec x, ← toθ_spec y, hxy]
  have hsurj : Function.Surjective toθ := by
    intro θ
    obtain ⟨Λ₂, hg, hth, hrel⟩ := bk θ.2.1 θ.2.2.1 θ.1 θ.2.2.2
    refine ⟨⟨Λ₂, hg, hth⟩, Subtype.ext (dd_ext H _ _ fun m₁ m₂ => ?_)⟩
    rw [toθ_spec, hrel]
  exact ⟨Equiv.ofBijective toθ ⟨hinj, hsurj⟩, toθ_spec⟩

end G3

end Formalism.L2.SG.LsDatumA
end
end

