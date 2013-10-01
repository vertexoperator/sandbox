#-*- coding:utf-8 -*-
"""
g94フォーマットの基底関数データを読み込む


基底関数セットは、例えば
EMSL Basis Set Exchange
https://bse.pnl.gov/bse/portal
で、様々なフォーマットで配布されている
"""
def readBasis_g94(fp):
    def float_g94(s):
        return float(s.replace('D' , 'e'))
    ret = {}
    atoms = [None , "H","He","Li","Be","B","C","N","O","F","Ne","Na","Mg","Al","Si","P","S","Cl","Ar",
             "K","Ca","Sc","Ti","V","Cr","Mn","Fe","Co","Ni","Cu","Zn","Ga","Ge","As","Se","Br","Kr",
             "Rb","Sr","Y","Zr","Nb","Mo","Tc","Ru","Rh","Pd"]
    lines = [line for line in fp if line[0]!='!' and len(line.strip())>0][1:]
    idx = 0
    while True:
        if idx==len(lines):break
        atomname = lines[idx].split()[0]
        assert(atomname in atoms),("未知の原子 %s" % atomname)
        atno = atoms.index(atomname)
        idx += 1
        ret[str(atno)] = []
        while True:
            ls = lines[idx].split()
            if len(ls)<2:
               idx+=1
               break
            orbtype = list(ls[0])
            contnum = int(ls[1])
            tmp = []
            for i in xrange(contnum):
               ls = lines[idx+i+1].split()
               norms = [(t,float_g94(v)) for (t,v) in zip(orbtype , ls[1:])]
               exponent = float_g94(ls[0])
               tmp.append( (exponent , norms) )
            ret[str(atno)].append( tmp )
            idx+=(contnum+1)
    return ret



"""
pdbファイルから原子の座標データを読む
"""
def readpdb(filename):
   def aux(s):
        pos=len(s)
        for n in xrange(1,10):
            _pos = s.find(str(n))
            if _pos<0:continue
            pos = min(pos,_pos)
        return s[:pos]
   atoms = [None , "H","He","Li","Be","B","C","N","O","F","Ne",
            "Na","Mg","Al","Si","P","S","Cl","Ar",
            "K","Ca","Sc","Ti","V","Cr","Mn","Fe","Co","Ni","Cu","Zn",
            "Ga","Ge","As","Se","Br","Kr"]
   def angstrom2bohr(r):
      return float(r)*1.8897261249935898
   ret = []
   for line in open(filename):
      ls = line.strip().split()
      if len(ls)<7:continue
      if ls[0]!="ATOM":continue
      assert(len(ls)>8 and len(ls)<11),("@pdb:%s %d個のカラム" % (filename,len(ls)))
      ret.append( (atoms.index(aux(ls[2])) , angstrom2bohr(ls[-5]) , angstrom2bohr(ls[-4]) , angstrom2bohr(ls[-3])) )
   return ret


