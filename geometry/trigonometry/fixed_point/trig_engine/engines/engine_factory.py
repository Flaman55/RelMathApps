from trig_engine.engines.exe_adapter import run_engine_exe

ENGINE_EXE = "./trig_engine_cli.exe"


from trig_engine.engines.exe_adapter import run_engine_exe

def make_engine(cfg, use_exe: bool):
    """
    Zwraca callable engine(**kw) o JEDNAKOWEJ sygnaturze
    niezależnie od backendu (python / exe).
    """

    if use_exe:
        # cfg zamknięte w klosurze
        def engine(**kw):
            return run_engine_exe(cfg, **kw)
        return engine

    else:
        # pythonowy silnik MA JUŻ poprawną sygnaturę
        return cfg["engine"]
