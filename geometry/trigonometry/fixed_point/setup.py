from setuptools import setup
from Cython.Build import cythonize
import os

# Ta konfiguracja skompiluje Twój silnik do nieczytelnej formy binarnej
setup(
    name='Relational Phase Engine',
    ext_modules=cythonize(f"trig_engine/engine_internal.py", 
        compiler_directives={'language_level': "3", 'always_allow_keywords': False}),
    zip_safe=False,
)