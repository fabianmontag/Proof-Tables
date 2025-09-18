import { useEffect, useState } from "react";

type FOLToken =
    | {
          type: "FORALL" | "EXISTS";
      }
    | {
          type: "AND" | "OR" | "NOT" | "IMPLIES" | "IFF";
      }
    | {
          type: "LP" | "RP" | "COL";
      }
    | {
          type: "ID";
          payload: string;
      }
    | {
          type: "CONST";
          payload: number;
      };

type ASTNode =
    | { type: "AND" | "OR" | "IMPLIES"; left: ASTNode; right: ASTNode }
    | { type: "ID"; payload: string }
    | { type: "CONST"; payload: number };

type ProofTableState =
    | {
          type: "table";
          context: ASTNode[];
          goal: ASTNode;
      }
    | {
          type: "endmark";
      };

const ASTtoString = (node: ASTNode): string => {
    if (node.type === "AND") {
        return ASTtoString(node.left) + " and " + ASTtoString(node.right);
    } else if (node.type === "OR") {
        return ASTtoString(node.left) + " or " + ASTtoString(node.right);
    } else if (node.type === "IMPLIES") {
        return ASTtoString(node.left) + " -> " + ASTtoString(node.right);
    } else if (node.type === "CONST") {
        return node.payload.toString();
    } else if (node.type === "ID") {
        return node.payload;
    }

    throw EvalError();
};

const ASTequals = (node1: ASTNode, node2: ASTNode): boolean => {
    let r = node1.type === node2.type;

    if (
        (node1.type === "AND" && node2.type === "AND") ||
        (node1.type === "OR" && node2.type === "OR") ||
        (node1.type === "IMPLIES" && node2.type === "IMPLIES")
    ) {
        r = r && ASTequals(node1.left, node2.left) && ASTequals(node1.right, node2.right);
    } else if ((node1.type === "ID" && node2.type === "ID") || (node1.type === "CONST" && node2.type === "CONST")) {
        r = r && node1.payload === node2.payload;
    } else {
        return false;
    }

    return r;
};

type Rule =
    | {
          type: "ImplIntro";
      }
    | {
          type: "OrIntro1";
      }
    | {
          type: "OrIntro2";
      }
    | {
          type: "AndIntro";
      }
    | {
          type: "AndElim";
          payload: number;
      }
    | {
          type: "OrElim";
          payload: number;
      }
    | {
          type: "Assumption";
          payload: number;
      };

const validateAndGetNext = (state: ProofTableState, appliedRule: Rule): ProofTableState[] => {
    if (state.type === "endmark") return [state];

    const { goal } = state;

    if (goal.type === "IMPLIES" && appliedRule.type === "ImplIntro") {
        return [{ context: [...state.context, goal.left], goal: goal.right, type: "table" }];
    } else if (goal.type === "OR" && appliedRule.type === "OrIntro1") {
        return [{ context: [...state.context], goal: goal.left, type: "table" }];
    } else if (goal.type === "OR" && appliedRule.type === "OrIntro2") {
        return [{ context: [...state.context], goal: goal.right, type: "table" }];
    } else if (goal.type === "AND" && appliedRule.type === "AndIntro") {
        return [
            { context: [...state.context], goal: goal.left, type: "table" },
            { context: [...state.context], goal: goal.right, type: "table" },
        ];
    } else if (appliedRule.type === "AndElim") {
        const h = state.context[appliedRule.payload];
        if (!h || h.type !== "AND") return [];
        return [{ context: [...state.context, h.left, h.right], goal: goal, type: "table" }];
    } else if (appliedRule.type === "OrElim") {
        const h = state.context[appliedRule.payload];
        if (!h || h.type !== "OR") return [];
        return [
            { context: [...state.context, h.left], goal: goal, type: "table" },
            { context: [...state.context, h.right], goal: goal, type: "table" },
        ];
    } else if (appliedRule.type === "Assumption") {
        const h = state.context[appliedRule.payload];
        if (!h || !ASTequals(state.goal, h)) return [];
        return [{ type: "endmark" }];
    }

    return [];
};

const isWhiteSpace = (c: string) => {
    return c === " ";
};

const isAlpha = (c: string) => {
    return ("a" <= c && c <= "z") || ("A" <= c && c <= "Z");
};

const isNumeric = (c: string) => {
    return "0" <= c && c <= "9";
};

export const isAlphaNumeric = (c: string) => {
    return isAlpha(c) || isNumeric(c);
};

const lexID = (lc: string[], currC: string): [string[], string] => {
    if (lc.length === 0) return [lc, currC];
    const c = lc.shift()!;
    if (isAlphaNumeric(c)) return lexID(lc, currC + c);
    else return [[c, ...lc], currC];
};

const lexNum = (lc: string[], currC: string): [string[], string] => {
    if (lc.length === 0) return [lc, currC];
    const c = lc.shift()!;
    if (isNumeric(c)) return lexID(lc, currC + c);
    else return [[c, ...lc], currC];
};

const lexFOL = (lc: string[]): FOLToken[] => {
    if (lc.length === 0) return [];
    const c = lc.shift()!;

    if (c === "-") {
        const c2 = lc.shift();
        if (c2 === ">") {
            return [{ type: "IMPLIES" }, ...lexFOL(lc)];
        } else {
            throw EvalError();
        }
    } else if (c === ":") {
        return [{ type: "COL" }, ...lexFOL(lc)];
    } else if (c === "(") {
        return [{ type: "LP" }, ...lexFOL(lc)];
    } else if (c === ")") {
        return [{ type: "RP" }, ...lexFOL(lc)];
    } else if (isAlpha(c)) {
        const [lcNew, id] = lexID(lc, c);

        if (id === "and") {
            return [{ type: "AND" }, ...lexFOL(lcNew)];
        } else if (id === "or") {
            return [{ type: "OR" }, ...lexFOL(lcNew)];
        } else if (id === "not") {
            return [{ type: "NOT" }, ...lexFOL(lcNew)];
        } else if (id === "forall") {
            return [{ type: "FORALL" }, ...lexFOL(lcNew)];
        } else if (id === "exists") {
            return [{ type: "EXISTS" }, ...lexFOL(lcNew)];
        }

        return [{ type: "ID", payload: id }, ...lexFOL(lcNew)];
    } else if (isNumeric(c)) {
        const [lcNew, id] = lexNum(lc, c);
        return [{ type: "CONST", payload: Number(id) }, ...lexFOL(lcNew)];
    } else if (isWhiteSpace(c)) return lexFOL(lc);

    throw EvalError();
};

const parseFOL = (ts: FOLToken[]) => {
    const parseSimple = (ts: FOLToken[]): [ASTNode, FOLToken[]] => {
        if (ts.length === 0) throw EvalError();
        const tkn = ts.shift()!;

        if (tkn.type === "CONST" || tkn.type === "ID") {
            return [tkn, ts];
        } else {
            throw EvalError();
        }
    };

    const parseBinary = (ts: FOLToken[]): [ASTNode, FOLToken[]] => {
        const parsePrec = (p: number, node: ASTNode, ts: FOLToken[]): [ASTNode, FOLToken[]] => {
            if (ts.length === 0) return [node, ts];
            const tkn = ts.shift()!;

            let lp, rp, kind;

            if (tkn.type === "AND") {
                [lp, rp, kind] = [10, 11, tkn.type];
            } else if (tkn.type === "OR") {
                [lp, rp, kind] = [10, 11, tkn.type];
            } else if (tkn.type === "IMPLIES") {
                [lp, rp, kind] = [5, 4, tkn.type];
            } else {
                // base case
                return [node, [tkn, ...ts]];
            }

            if (lp < p) {
                return [node, [tkn, ...ts]];
            } else {
                const [nodeR, ts2] = parsePrec(rp, ...parseSimple(ts));
                return parsePrec(p, { type: kind, left: node, right: nodeR }, ts2);
            }
        };

        return parsePrec(0, ...parseSimple(ts));
    };

    const [n, tsp] = parseBinary(ts);

    console.log(tsp);
    if (tsp.length !== 0) throw EvalError();

    return n;
};

type ProofTableComponentProps = {
    proofTableState: ProofTableState;
};

const ProofTableComponent: React.FC<ProofTableComponentProps> = ({ proofTableState }) => {
    const [childProofTables, setChildProofTables] = useState<ProofTableState[]>([]);
    const [rule, setRule] = useState<Rule>({ type: "ImplIntro" });
    const [assumptionLabel1, setAssumptionLabel1] = useState<number>(0);

    const handleApplyRule = () => {
        setChildProofTables(validateAndGetNext(proofTableState, rule));
    };

    const handleChangeRule = (e: React.ChangeEvent<HTMLSelectElement>) => {
        const value = e.target.value;

        if (value === "AndIntro" || value === "OrIntro1" || value === "OrIntro2" || value === "ImplIntro") {
            setRule({ type: value });
        } else if (value === "Assumption" || value === "AndElim" || value === "OrElim") {
            setRule({ type: value, payload: assumptionLabel1 });
        }
    };

    const handleUndoStep = () => {
        setChildProofTables([]);
    };

    const handleAssumptionLabel1Change = (e: React.ChangeEvent<HTMLInputElement>) => {
        const value = e.target.value;
        setAssumptionLabel1(Number(value));
    };

    useEffect(() => {
        if (rule.type === "Assumption") {
            setRule({ ...rule, payload: assumptionLabel1 });
        }
    }, [assumptionLabel1]);

    return (
        <div className="w-full h-auto">
            {proofTableState.type === "endmark" ? (
                <div className="w-full h-auto border p-1"></div>
            ) : (
                <>
                    <div className="w-auto h-auto flex flex-row items-stretch justify-center border">
                        <div className="w-full h-auto flex flex-col items-center justify-center p-1 border-r">
                            {proofTableState.context.map((e, i) => (
                                <p key={i}>{"H" + i + ": " + ASTtoString(e)}</p>
                            ))}
                        </div>
                        <p className="w-full h-auto flex flex-row items-center justify-center p-1 border-r">
                            {ASTtoString(proofTableState.goal)}
                        </p>
                        <div className="w-full h-auto flex flex-row items-center justify-center gap-2 p-1">
                            <select onChange={handleChangeRule} value={rule.type}>
                                <option value="ImplIntro">ImplIntro</option>
                                <option value="AndIntro">AndIntro</option>
                                <option value="OrIntro1">OrIntro1</option>
                                <option value="OrIntro2">OrIntro2</option>
                                <option value="Assumption">Assumption</option>
                                <option value="AndElim">AndElim</option>
                                <option value="OrElim">OrElim</option>
                            </select>
                            {rule.type === "Assumption" && (
                                <input
                                    type="number"
                                    className="w-12"
                                    value={assumptionLabel1}
                                    onChange={handleAssumptionLabel1Change}
                                />
                            )}
                            <button className="border px-2 cursor-pointer" onClick={handleApplyRule}>
                                apply
                            </button>
                            <button
                                className="border px-2 cursor-pointer disabled:opacity-50"
                                disabled={childProofTables.length === 0}
                                onClick={handleUndoStep}
                            >
                                undo
                            </button>
                        </div>
                    </div>
                    <div className="w-full h-auto flex flex-row items-start">
                        {childProofTables.map((e, i) => (
                            <ProofTableComponent proofTableState={e} key={i} />
                        ))}
                    </div>
                </>
            )}
        </div>
    );
};

const getFOLAST = (s: string) => {
    console.log(lexFOL(s.split("")));
    console.log(parseFOL(lexFOL(s.split(""))));

    return parseFOL(lexFOL(s.split("")));
};

function App() {
    const [goalText, setGoalText] = useState("A or B -> A or B");
    const [goal, setGoal] = useState<ASTNode | null>(null);

    useEffect(() => {
        try {
            setGoal(getFOLAST(goalText));
        } catch (error) {
            setGoal(null);
        }
    }, [goalText]);

    const handleGoalChange = (e: React.ChangeEvent<HTMLInputElement>) => {
        setGoalText(e.target.value);
    };

    return (
        <div className="w-full h-screen bg-neutral-600 border-neutral-500 text-white">
            <input value={goalText} onInput={handleGoalChange} />
            {goal ? (
                <ProofTableComponent proofTableState={{ goal, context: [], type: "table" }} />
            ) : (
                <p>unable to parse goal</p>
            )}
        </div>
    );
}

export default App;
