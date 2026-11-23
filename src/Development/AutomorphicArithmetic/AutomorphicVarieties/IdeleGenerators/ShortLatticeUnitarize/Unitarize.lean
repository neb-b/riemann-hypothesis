module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CmpResplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V.Af
open scoped Matrix NNReal

namespace UpperTheory.V.Sd.Wc

def WtMon : Prop :=
  ∀ (I : Type) [Fintype I] (n : I → ℕ) (P : MvPolynomial (I × Fin 2) ℂ), P ∈ Wt n ↔ ∀ d ∈ P.support, ∀ v, d (v, 0) + d (v, 1) = n v

def ExChi : Prop :=
  ∀ (G Z : Type) [Group G] [Group Z] (K : Subgroup G) (ζ : Z →* G) (ω : Z →* ℂˣ), (∀ z, ζ z ∈ Subgroup.center G) → (∀ z, ζ z ∈ K → ω z = 1) →
    ∃ χ : ↥(K ⊔ ζ.range) →* ℂˣ, ∀ h : ↥(K ⊔ ζ.range), (∃ k ∈ K, ∃ z, (h : G) = k * ζ z) ∧ ∀ k ∈ K, ∀ z, (h : G) = k * ζ z → χ h = ω z

def KcTop : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    (∀ c : Pl F → ℕ, {w | c w ≠ 0}.Finite → IsOpen (Kc c : Set (GF F)) ∧ IsCompact (Kc c : Set (GF F))) ∧
    (∀ U ∈ nhds (1 : GF F), ∃ L : Subgroup (GF F), IsOpen (L : Set (GF F)) ∧ (L : Set (GF F)) ⊆ U) ∧
    (∀ z, zc F z ∈ Subgroup.center (GF F)) ∧ IsClosed ((zc F).range : Set (GF F)) ∧ Continuous (zc F) ∧
    ∀ (c : Pl F → ℕ) (w : Pl F), ∀ k ∈ K1 w (c w), locGL F 2 w k ∈ Kc c

def FixGlob : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V), GlobalTheory.PRep.IsSmooth ρ →
    ∀ (c : Pl F → ℕ) (x : V), (∀ w, x ∈ Hi.fixd (ρ.comp (locGL F 2 w)) (K1 w (c w))) → x ∈ Hi.fixd ρ (Kc c)

def HkReps : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (c : ℕ), ∃ (N : ℕ) (a : Fin N → GL (Fin 2) (w.adicCompletion F)),
    (c ≠ 0 → ∀ i, ∃ u : w.adicCompletionIntegers F, a i = aff (atFin w (unif w)) (u : w.adicCompletion F)) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V), ∀ x ∈ Hi.fixd ρ (K1 w c),
      Uop w ρ c x ∈ Hi.fixd ρ (K1 w c) ∧ Uop w ρ c x = ∑ i, ρ (a i) x

def HkComm : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V) (c : Pl F → ℕ),
    ∀ x ∈ Hi.fixd ρ (Kc c), ∀ w, Uop w (ρ.comp (locGL F 2 w)) (c w) x ∈ Hi.fixd ρ (Kc c) ∧
      ∀ w', Uop w (ρ.comp (locGL F 2 w)) (c w) (Uop w' (ρ.comp (locGL F 2 w')) (c w') x) =
        Uop w' (ρ.comp (locGL F 2 w')) (c w') (Uop w (ρ.comp (locGL F 2 w)) (c w) x)

def ExL : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), SplitL F l → Nonempty (LDat F ι)


open Classical in
def GlFacts : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (D : LDat F ι),
    (∀ c : Pl F → ℕ, (∀ v, c (D.pl v) = 1) →
      (∀ k ∈ Kc c, ∀ v, (∀ i j, nu ι ((D.gl k v : Matrix (Fin 2) (Fin 2) ℂ) i j) ≤ 1) ∧ nu ι ((D.gl k v : Matrix (Fin 2) (Fin 2) ℂ) 1 0) < 1 ∧
        nu ι ((D.gl k v : Matrix (Fin 2) (Fin 2) ℂ) 1 1 - 1) < 1 ∧ nu ι (D.gl k v : Matrix (Fin 2) (Fin 2) ℂ).det = 1 ∧
        nu ι ((D.gl k v : Matrix (Fin 2) (Fin 2) ℂ).det ^ (l - 1) - 1) < 1) ∧
      ∀ a : InfinitePlace F → ℕ, ∃ k ∈ Kc c, ∀ v, (D.gl k v : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; ((l * a v : ℕ) : ℂ), 1]) ∧
    (∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ a, D.gl (locGL F 2 w a) = 1) ∧
    (∀ v a, D.gl (locGL F 2 (D.pl v) a) = Pi.mulSingle v (Matrix.GeneralLinearGroup.map (D.em v) a)) ∧
    (∀ (n : InfinitePlace F → ℕ) (e : InfinitePlace F → ℤ) z x,
      D.R n e (zc F z) x = (∏ v, D.ea v (z : Af F) ^ ((n v : ℤ) + 2 * e v)) • x) ∧
    (∀ e w, nu ι (D.uf e w) = 1) ∧
    ∀ e e' : InfinitePlace F → ℤ, (∀ v, ((l : ℤ) - 1) ∣ e' v - e v) → ∀ w, nu ι (D.uf e' w - D.uf e w) < 1

def LocTwo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (u : Pl F) (c : ℕ), c ≠ 0 → normV u = 2 → ∀ k ∈ K1 u c, ∀ n : ℕ, Odd n →
    k ^ n ∈ Subgroup.center (GL (Fin 2) (u.adicCompletion F)) → k ∈ Subgroup.center (GL (Fin 2) (u.adicCompletion F))

def CentChar : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2), ∃ ω : HChar F,
    (∀ (z : Ideles F), ∀ φ ∈ π.V, ∀ g, φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) ∧
    ∀ z x, π.finPart (zc F z) x = ((ω.1 (finId F z) : ℂˣ) : ℂ) • x

def PolGL2 : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (ω : HChar F),
    (∀ (z : Ideles F), ∀ φ ∈ π.V, ∀ g, φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) → π.IsSelfDualBy ω

end UpperTheory.V.Sd.Wc
