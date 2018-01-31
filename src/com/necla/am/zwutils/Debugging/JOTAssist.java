
package com.necla.am.zwutils.Debugging;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeSet;
import java.util.logging.Level;

import com.necla.am.zwutils.Debugging.ObjectTrap.IHook;
import com.necla.am.zwutils.Logging.GroupLogger;
import com.necla.am.zwutils.Logging.IGroupLogger;
import com.necla.am.zwutils.Misc.Misc;
import com.necla.am.zwutils.Reflection.IClassSolver;
import com.necla.am.zwutils.Reflection.IClassSolver.Impl.DirectClassSolver;
import com.necla.am.zwutils.Reflection.PackageClassIterable;
import com.necla.am.zwutils.Reflection.SuffixClassDictionary;
import com.necla.am.zwutils.Reflection.SuffixClassDictionary.DirectSuffixClassSolver;

import jline.console.ConsoleReader;
import jline.console.completer.Completer;


public class JOTAssist {
	
	public static final String LogGroup = "ZWUtils.Debugging.JOTAssist";
	protected static final IGroupLogger CLog = new GroupLogger(LogGroup);
	
	public final IClassSolver TapClass;
	public final SuffixClassDictionary TapPackage;
	public final Map<Class<?>, List<Class<?>>> ClassDescMap;
	
	public final Completer ClassCompleter;
	public final Completer FieldCompleter;
	public final Completer GetterCompleter;
	public final Completer SymbolCompleter;
	
	protected final ObjectTrap JOT;
	protected IClassSolver CurClass;
	
	public JOTAssist(String jarpath, String cname, String pkgname)
			throws IOException, ClassNotFoundException {
		URL FileURL = new File(jarpath).toURI().toURL();
		URL JarURL = new URL("jar", "", FileURL.toString());
		ClassLoader Loader = new URLClassLoader(Misc.wrap(FileURL));
		
		SuffixClassDictionary ClassDict = new SuffixClassDictionary(jarpath, Loader);
		DirectSuffixClassSolver.EnumBaseClassSolvers(ClassDict::Add);
		new PackageClassIterable(JarURL, "", null).forEach(ClassDict::Add);
		CLog.Info("Loaded %d classes from Jar", ClassDict.size());
		
		if (cname != null) {
			TapClass = ClassDict.Get(cname);
			if (pkgname == null) {
				if (DirectSuffixClassSolver.FilterBaseClassSolvers(C -> !TapClass.equals(C))) {
					pkgname = TapClass.toClass().getPackage().getName();
				}
			}
			CLog.Info("Located base class '%s' (%s)", TapClass.toString(), TapClass.FullName());
		} else {
			TapClass = DirectSuffixClassSolver.OBJECT;
		}
		
		if (pkgname != null) {
			TapPackage = new SuffixClassDictionary(jarpath, Loader);
			new PackageClassIterable(JarURL, pkgname, null).forEach(clsname -> {
				CLog.Fine(":+ %s ", clsname);
				TapPackage.Add(clsname);
			});
			CLog.Info("Loaded %d classes under target package '%s'", TapPackage.size(), pkgname);
			JOT = new ObjectTrap(TapClass.toClass(), pkgname, Loader);
		} else {
			TapPackage = ClassDict;
			JOT = new ObjectTrap(TapClass.toClass(), "", Loader);
		}
		
		CurClass = TapClass;
		ClassDescMap = new HashMap<>();
		
		int SuperCnt = 0;
		Stack<Class<?>> SCS = new Stack<>();
		for (IClassSolver CS : TapPackage) {
			Class<?> C = CS.toClass();
			CLog.Fine(":%s", C);
			Class<?> SC = C.getSuperclass();
			while (SC != null) {
				CLog.Fine(": extends %s", SC);
				List<Class<?>> DescList = ClassDescMap.get(SC);
				if (DescList == null) {
					DescList = new ArrayList<>();
					ClassDescMap.put(SC, DescList);
				}
				DescList.add(C);
				SC = SC.getSuperclass();
				SuperCnt++;
			}
			SCS.addAll(Arrays.asList(C.getInterfaces()));
			Class<?> SI = !SCS.isEmpty()? SCS.pop() : null;
			while (SI != null) {
				if (C.isInterface()) {
					CLog.Fine(": extends %s", SI);
				} else {
					CLog.Fine(": implements %s", SI);
				}
				List<Class<?>> DescList = ClassDescMap.get(SI);
				if (DescList == null) {
					DescList = new ArrayList<>();
					ClassDescMap.put(SI, DescList);
				}
				DescList.add(C);
				SuperCnt++;
				SCS.addAll(Arrays.asList(SI.getInterfaces()));
				SI = !SCS.isEmpty()? SCS.pop() : null;
			}
		}
		CLog.Info("Discovered %d ancestry relations", SuperCnt);
		
		ClassCompleter = new Completer() {
			
			IClassSolver CacheClass = null;
			Set<String> CandiCName = new TreeSet<>();
			
			@Override
			public int complete(String buffer, int cursor, List<CharSequence> candidates) {
				if (cursor <= 0) return -1;
				if (buffer.isEmpty()) return -1;
				
				String PartBuf = buffer.substring(0, cursor);
				if (PartBuf.charAt(0) != ObjectTrap.SYM_ASCLASS) return -1;
				if (PartBuf.indexOf(ObjectTrap.SYM_FIELD) > 0) return -1;
				if (PartBuf.indexOf(ObjectTrap.SYM_GETTER) > 0) return -1;
				
				if (!CurClass.equals(CacheClass)) {
					CandiCName.clear();
					try {
						List<Class<?>> DescList = ClassDescMap.get(CurClass.toClass());
						if (DescList != null) {
							DescList.forEach(C -> {
								IClassSolver DictClass = TapPackage.Lookup(C.getName());
								if (DictClass == null) {
									DictClass = new DirectClassSolver(C);
								}
								CandiCName.add(DictClass.toString());
							});
							CLog.Fine("Loaded %d derivative classes", DescList.size());
						}
					} catch (ClassNotFoundException e) {
						Misc.CascadeThrow(e);
					}
					CacheClass = CurClass;
				}
				
				String PartCName = PartBuf.substring(1);
				List<CharSequence> NewComplete = new ArrayList<>();
				CandiCName.forEach(CName -> {
					if (CName.startsWith(PartCName)) {
						NewComplete.add(ObjectTrap.SYM_ASCLASS + CName);
					}
				});
				if (NewComplete.size() == 1) {
					if (NewComplete.get(0).equals(PartBuf)) {
						NewComplete.clear();
					}
				}
				candidates.addAll(NewComplete);
				return -1;
			}
			
		};
		
		FieldCompleter = new Completer() {
			
			IClassSolver CacheClass = null;
			Set<String> CandiFName = new TreeSet<>();
			
			@Override
			public int complete(String buffer, int cursor, List<CharSequence> candidates) {
				if (cursor <= 0) return -1;
				if (buffer.isEmpty()) return -1;
				
				String PartBuf = buffer.substring(0, cursor);
				int FieldIdx = PartBuf.indexOf(ObjectTrap.SYM_FIELD);
				if (FieldIdx < 0) return -1;
				
				String ParseBuf = PartBuf;
				IClassSolver WorkingClass = CurClass;
				if (PartBuf.charAt(0) == ObjectTrap.SYM_ASCLASS) {
					String PartCName = ParseBuf.substring(1, FieldIdx);
					ParseBuf = ParseBuf.substring(FieldIdx);
					
					if (!TapPackage.isKnown(PartCName)) return -1;
					if (TapPackage.isAmbigious(PartCName)) return -1;
					WorkingClass = TapPackage.Get(PartCName);
				}
				
				if (!WorkingClass.equals(CacheClass)) {
					CandiFName.clear();
					List<Class<?>> CandiClass = new ArrayList<>();
					try {
						Class<?> C = WorkingClass.toClass();
						while (C != null) {
							CandiClass.add(C);
							C = C.getSuperclass();
						}
						CLog.Fine("Loaded %d super classes", CandiClass.size());
						CandiClass.forEach(CC -> {
							for (Field F : CC.getDeclaredFields()) {
								CandiFName.add(F.getName());
							}
						});
						CLog.Fine("Loaded %d field names", CandiFName.size());
					} catch (ClassNotFoundException e) {
						Misc.CascadeThrow(e);
					}
					CacheClass = WorkingClass;
				}
				
				if (ParseBuf.charAt(0) != ObjectTrap.SYM_FIELD) return -1;
				String PartFName = ParseBuf.substring(1);
				String PrevPart = PartBuf.substring(0, FieldIdx + 1);
				List<CharSequence> NewComplete = new ArrayList<>();
				CandiFName.forEach(FName -> {
					if (FName.startsWith(PartFName)) {
						NewComplete.add(PrevPart + FName);
					}
				});
				if (NewComplete.size() == 1) {
					if (NewComplete.get(0).equals(PartBuf)) {
						NewComplete.clear();
					}
				}
				candidates.addAll(NewComplete);
				return -1;
			}
			
		};
		
		GetterCompleter = new Completer() {
			
			IClassSolver CacheClass = null;
			Set<String> CandiGName = new TreeSet<>();
			
			@Override
			public int complete(String buffer, int cursor, List<CharSequence> candidates) {
				if (cursor <= 0) return -1;
				if (buffer.isEmpty()) return -1;
				
				String PartBuf = buffer.substring(0, cursor);
				int GetterIdx = PartBuf.indexOf(ObjectTrap.SYM_GETTER);
				if (GetterIdx < 0) return -1;
				
				String ParseBuf = PartBuf;
				IClassSolver WorkingClass = CurClass;
				if (PartBuf.charAt(0) == ObjectTrap.SYM_ASCLASS) {
					String PartCName = ParseBuf.substring(1, GetterIdx);
					ParseBuf = ParseBuf.substring(GetterIdx);
					
					if (!TapPackage.isKnown(PartCName)) return -1;
					if (TapPackage.isAmbigious(PartCName)) return -1;
					WorkingClass = TapPackage.Get(PartCName);
				}
				
				if (!WorkingClass.equals(CacheClass)) {
					CandiGName.clear();
					List<Class<?>> CandiClass = new ArrayList<>();
					try {
						Stack<Class<?>> SCS = new Stack<>();
						Class<?> C = WorkingClass.toClass();
						while (C != null) {
							CandiClass.add(C);
							SCS.addAll(Arrays.asList(C.getInterfaces()));
							if ((C = C.getSuperclass()) == null) {
								C = !SCS.isEmpty()? SCS.pop() : null;
							}
						}
						CLog.Fine("Loaded %d super classes/interfaces", CandiClass.size());
						for (Class<?> CC : CandiClass) {
							for (Method M : CC.getDeclaredMethods())
								if ((M.getParameterTypes().length == 0) && !M.getReturnType().equals(Void.TYPE)) {
									CandiGName.add(M.getName());
								}
						}
						CLog.Fine("Loaded %d getter names", CandiGName.size());
					} catch (ClassNotFoundException e) {
						Misc.CascadeThrow(e);
					}
					CacheClass = WorkingClass;
				}
				
				if (ParseBuf.charAt(0) != ObjectTrap.SYM_GETTER) return -1;
				String PartGName = ParseBuf.substring(1);
				String PrevPart = PartBuf.substring(0, GetterIdx + 1);
				List<CharSequence> NewComplete = new ArrayList<>();
				CandiGName.forEach(GName -> {
					if (GName.startsWith(PartGName)) {
						NewComplete.add(PrevPart + GName);
					}
				});
				if (NewComplete.size() == 1) {
					if (NewComplete.get(0).equals(PartBuf)) {
						NewComplete.clear();
					}
				}
				candidates.addAll(NewComplete);
				return -1;
			}
			
		};
		
		SymbolCompleter = (buffer, cursor, candidates) -> {
			if (buffer.isEmpty() || (cursor <= 0)) {
				candidates.add(String.valueOf(ObjectTrap.SYM_ASCLASS)); // As Class
				candidates.add(String.valueOf(ObjectTrap.SYM_ASTYPE)); // As Type
				candidates.add(String.valueOf(ObjectTrap.SYM_FIELD)); // Field
				candidates.add(String.valueOf(ObjectTrap.SYM_GETTER)); // Getter
				candidates.add(String.valueOf(ObjectTrap.SYM_SCOPEOP)); // Operation
				return -1;
			}
			
			String PartBuf = buffer.substring(0, cursor);
			String ParseBuf = PartBuf;
			String PartCName = null;
			while (ParseBuf.charAt(0) == ObjectTrap.SYM_ASCLASS) {
				int NextTok = ParseBuf.indexOf(ObjectTrap.SYM_FIELD);
				if (NextTok > 0) {
					PartCName = ParseBuf.substring(1, NextTok);
					ParseBuf = ParseBuf.substring(NextTok - 1);
					break;
				}
				NextTok = ParseBuf.indexOf(ObjectTrap.SYM_GETTER);
				if (NextTok > 0) {
					PartCName = ParseBuf.substring(1, NextTok);
					ParseBuf = ParseBuf.substring(NextTok - 1);
					break;
				}
				
				PartCName = ParseBuf.substring(1);
				if (!TapPackage.isKnown(PartCName)) return -1;
				if (TapPackage.isAmbigious(PartCName)) return -1;
				
				candidates.add(PartBuf + ObjectTrap.SYM_FIELD);
				candidates.add(PartBuf + ObjectTrap.SYM_GETTER);
				return -1;
			}
			
			return -1;
		};
	}
	
	protected static class ScopeDesc {
		public IClassSolver C = null;
		public Method G = null;
		public Field F = null;
		public ObjectTrap.CastableTypes T = null;
	}
	
	ScopeDesc GetScopeDesc(String Scope) throws SecurityException, ClassNotFoundException {
		ScopeDesc Desc = new ScopeDesc();
		while ((Scope != null) && !Scope.isEmpty()) {
			switch (Scope.charAt(0)) {
				case ObjectTrap.SYM_ASTYPE: {
					if ((Desc.C != null) || (Desc.F != null) || (Desc.G != null) || (Desc.T != null)) {
						Misc.ERROR("Excessive scope");
					}
					
					if (Scope.length() != 2) {
						Misc.ERROR("Invalid type case scope");
					}
					ObjectTrap.TypeCastScope TS = JOT.new TypeCastScope(Scope.charAt(1));
					Desc.T = TS.T;
					Scope = null;
					break;
				}
				case ObjectTrap.SYM_ASCLASS: {
					if ((Desc.C != null) || (Desc.F != null) || (Desc.G != null) || (Desc.T != null)) {
						Misc.ERROR("Excessive scope");
					}
					
					int PartIdx = Scope.indexOf(ObjectTrap.SYM_FIELD);
					if (PartIdx < 0) {
						PartIdx = Scope.indexOf(ObjectTrap.SYM_GETTER);
					}
					if (PartIdx < 0) {
						Misc.ERROR("Incomplete scope");
					}
					
					String PartCName = Scope.substring(1, PartIdx);
					Desc.C = TapPackage.Get(PartCName);
					
					Scope = Scope.substring(PartIdx);
					break;
				}
				case ObjectTrap.SYM_FIELD: {
					if ((Desc.F != null) || (Desc.G != null) || (Desc.T != null)) {
						Misc.ERROR("Excessive scope");
					}
					
					ObjectTrap.FieldScope FS = JOT.new FieldScope(
							Desc.C != null? Desc.C.toClass() : CurClass.toClass(), null, Scope.substring(1));
					Desc.F = FS.F;
					Scope = null;
					break;
				}
				case ObjectTrap.SYM_GETTER: {
					if ((Desc.F != null) || (Desc.G != null) || (Desc.T != null)) {
						Misc.ERROR("Excessive scope");
					}
					
					ObjectTrap.GetterScope GS = JOT.new GetterScope(
							Desc.C != null? Desc.C.toClass() : CurClass.toClass(), null, Scope.substring(1));
					Desc.G = GS.M;
					Scope = null;
					break;
				}
				default:
					Misc.ERROR("Malformed scope");
			}
		}
		return Desc;
	}
	
	@SuppressWarnings("unchecked")
	public static void main(String args[]) {
		try {
			if (args.length < 1) {
				Misc.ERROR("Please specify pathname to target Jar!");
			}
			String jarpath = args[0];
			String cname = args.length < 2? null : args[1];
			String pkgname = args.length < 3? null : args[2];
			if (args.length > 3) {
				CLog.Warn("Ignored %d excessive arguments", args.length - 3);
			}
			
			JOTAssist Assist = new JOTAssist(jarpath, cname, pkgname);
			List<ScopeDesc> ScopeCascade = new ArrayList<>();
			
			ConsoleReader console = new ConsoleReader();
			console.setHandleUserInterrupt(true);
			console.setExpandEvents(false);
			
			console.addCompleter(Assist.SymbolCompleter);
			console.addCompleter(Assist.ClassCompleter);
			console.addCompleter(Assist.FieldCompleter);
			console.addCompleter(Assist.GetterCompleter);
			console.addCompleter((buffer, cursor, candidates) -> {
				if (cursor <= 0) return -1;
				if (buffer.isEmpty()) return -1;
				
				String PartBuf = buffer.substring(0, cursor);
				if (PartBuf.charAt(0) != ObjectTrap.SYM_ASTYPE) return -1;
				if (PartBuf.length() > 1) return -1;
				
				for (ObjectTrap.CastableTypes T : ObjectTrap.CastableTypes.values()) {
					candidates.add(String.format("%c%c", ObjectTrap.SYM_ASTYPE, T.SYMBOL));
				}
				
				return -1;
			});
			console.addCompleter((buffer, cursor, candidates) -> {
				if (cursor <= 0) return -1;
				if (buffer.isEmpty()) return -1;
				
				String PartBuf = buffer.substring(0, cursor);
				if (PartBuf.charAt(0) != ObjectTrap.SYM_SCOPEOP) return -1;
				if (PartBuf.length() > 2) return -1;
				
				try {
					Class<?> HC = ObjectTrap.HookMaker.Lookup(Assist.CurClass.toClass());
					if (HC == null) return -1;
					
					String OpBuf = buffer.substring(1);
					Method HM = HC.getDeclaredMethod("InputHelp");
					((Collection<String>) HM.invoke(null)).forEach(HH -> {
						if (HH.startsWith(OpBuf)) {
							candidates.add(ObjectTrap.SYM_SCOPEOP + HH);
						}
					});
				} catch (Exception e) {
					return -1;
				}
				
				return -1;
			});
			console.addCompleter((buffer, cursor, candidates) -> candidates.isEmpty()? -1 : 0);
			
			PrintWriter cout = new PrintWriter(console.getOutput());
			cout.println("Scope: " + GetScopeString(ScopeCascade) + " [" + Assist.CurClass + "] ");
			cout.flush();
			String LineIn;
			while ((LineIn = console.readLine()) != null) {
				try {
					if (LineIn.isEmpty()) {
						if (ScopeCascade.size() > 0) {
							ScopeCascade.remove(ScopeCascade.size() - 1);
						} else {
							cout.println("* Already at root level!");
						}
					} else {
						if (LineIn.charAt(0) != ObjectTrap.SYM_SCOPEOP) {
							ScopeCascade.add(Assist.GetScopeDesc(LineIn));
						} else {
							IHook H = ObjectTrap.HookMaker.Create(Assist.CurClass.toClass(), LineIn.substring(1),
									Assist.TapPackage);
							cout.print("Hook operation: ");
							cout.println(H.toString());
						}
					}
					
					if (!ScopeCascade.isEmpty()) {
						ScopeDesc SD = ScopeCascade.get(ScopeCascade.size() - 1);
						Class<?> CC = ((SD.T != null)? SD.T.CLASS : (SD.F != null)? SD.F
								.getType() : (SD.G != null)? SD.G.getReturnType() : null);
						if (CC == null) {
							Misc.FAIL("Internal Error - Unable to derive current type");
						}
						
						Assist.CurClass = Assist.TapPackage.Lookup(CC.getName());
						if (Assist.CurClass == null) {
							Assist.CurClass = new DirectClassSolver(CC);
						}
					} else {
						Assist.CurClass = Assist.TapClass;
					}
					cout.println("Scope: " + GetScopeString(ScopeCascade) + " [" + Assist.CurClass + "] ");
				} catch (Throwable e) {
					String ErrMsg = String.format("* Unable to parse input - %s ", e);
					if (e.getCause() != null) {
						ErrMsg += " - " + e.getCause();
					}
					cout.println(ErrMsg);
					if (CLog.isLoggable(Level.FINE)) {
						CLog.logExcept(e);
					}
					cout.println("Scope: " + GetScopeString(ScopeCascade) + " [" + Assist.CurClass + "] ");
					console.putString(LineIn);
				}
				cout.flush();
			}
			cout.println();
			cout.flush();
		} catch (Throwable e) {
			CLog.logExcept(e);
		}
	}
	
	private static String GetScopeString(List<ScopeDesc> scopes) {
		StringBuilder StrBuf = new StringBuilder();
		
		scopes.forEach(desc -> {
			if (StrBuf.length() != 0) {
				StrBuf.append(ObjectTrap.SYM_SCOPES);
			}
			if (desc.T != null) {
				StrBuf.append(ObjectTrap.SYM_ASTYPE);
				StrBuf.append(desc.T.SYMBOL);
			} else {
				if (desc.C != null) {
					StrBuf.append(ObjectTrap.SYM_ASCLASS);
					StrBuf.append(desc.C.toString());
				}
				if (desc.F != null) {
					StrBuf.append(ObjectTrap.SYM_FIELD);
					StrBuf.append(desc.F.getName());
				}
				if (desc.G != null) {
					StrBuf.append(ObjectTrap.SYM_GETTER);
					StrBuf.append(desc.G.getName());
				}
			}
		});
		
		return StrBuf.length() > 0? StrBuf.toString() : "(Root)";
	}
}
