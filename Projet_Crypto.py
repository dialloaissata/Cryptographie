import math
import decimal
from itertools import zip_longest

from Crypto.Cipher import AES, PKCS1_OAEP
from Crypto.Random import get_random_bytes
from Crypto.Hash import SHA256
from Crypto.PublicKey import RSA
from Crypto.Cipher import PKCS1_v1_5

import binascii
import chardet

import matplotlib.pyplot as plt
import numpy as np

import base64
import hashlib
from cryptography.fernet import Fernet
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC

#Dechiffrer le certificat de Bob
def dechiffrer_rsa(message_chiffre, d, n):
  # Initialiser une liste vide pour stocker les caractères déchiffrés
  caracteres_dec = []
  for c in message_chiffre:
    m = pow(c, d, n)
    print(m)
    octets = m.to_bytes((m.bit_length() + 7) // 8, 'big')
    # Ajouter les trois caractères correspondants à la liste
    caracteres_dec.extend(chr(b) for b in octets)
  # Renvoyer le message déchiffré en tant que chaîne de caractères
  return ''.join(caracteres_dec)

#Test de la fonction
message = [278799152, 90156592, 58604019, 270790021, 191655934, 77354476, 20168774, 34746869, 95017699, 146257886, 20516056, 109102945, 43312681, 210513261, 168559761, 209629430, 31567550, 186256911, 264106209, 90156592, 167226088, 253248213, 230642899, 223555714, 45616415, 39373110, 115053379, 107664230, 54263416, 62063702, 236662954, 94508130 ]
print(dechiffrer_rsa(message, 1231, 279455989))

#Resultat de la question 1
#Bob est bien celui qu'il pretend etre, et sa cle publique est (e,n)=(1451,2517761299) en decimal
#clé public de BOB: (e,n)=(1451,2517761299)


#Trouver la clé privé de Bob, Calcul en ligne(lien dans le rapport)
print("\nClé privée de BOB: d = ", 2042319124)
#clé privé de BOB: l'inverse de e, d= 2042319124


#Calcul du CardE (Cette méthode ne donne pas la bonne valeur, calcul en ligne, lien dans le rapport)
# Courbe elliptique de Bob: y^2=x^3+6x+6, modulo p=11161. 

t = 6 # nombre de point de torsion de la courbe
p = 11161
card_E = (p + 1) - t # ordre de E

print("\nordre de la courbe élliptique (card-E): ", card_E )
#card_E = 11275 5Reponse du lien)

#Trouver y_g du point G

def find_y(x, a, b, p):
  # Calculez le membre de droite de l'équation de la courbe
  right = (pow(x,3) + a*x + b) % p
  for i in range(0,p//2):
    if(pow(i,2)%p == right):
        yG = i
        break
  y2 = p - yG
  return yG,y2

yG, y2 = find_y(17, 6, 6, 11161)

# Affichez les valeurs de y1 et y2
print("\nyG =", yG)
print("y2 =" ,y2)

#yG = 2802 on choisit cette valeur parceque c'est elle qui est compris entre 0 et p/2
#y2 = 8359


#Calcul de a et ordre de G

# E: y^2 = x^3 + 6x + 6 (mod 11161)  
p = 11161
a = 6
b = 6
# point initial (x1,y1)=(17,2802)
x1 = x2 = 17
y1 = y2 = 2802
for i in range(2, 20000):
   val = 0
   if (x1 == x2):
       # points identiques (pour determiner k)
       val = ((3 * (x1 ** 2) + a) * pow(2 * y1, p-2, p))%p
       if(x1==17 and i!=2):
        print("\nvaleur possible pour k : ", i)
   else:
       # points distincts (pour determiner a)
       val = ((y2 - y1) * pow(x2 - x1, p-2, p))%p
   # calcule de i.G
   x3 = (val ** 2 - x1 - x2) % p
   y3 = (val*(x1 - x3) - y1) % p
   if(x3==6179 and y3==5635):
      print("\nvaleur possible pour a : ",str(i) + "\t")
   (x2, y2) = (x3, y3)

# valeur de a = 1786 et 13059 mais on prend la valeur la plus petite
# valeur de k= 11275


#Clé E.C.D.H. d'Alice : bP = (9557,9197) 
#Abscisse x du secret partagé abG=(x,y)

INF_POINT = None
# a, b p represente les parametres de la courbe elliptique, la fonction est le constructeur de la classe, initialise les valeurs
class EllipticCurve:
  def __init__(self, a, b, p):
      self.a = a
      self.b = b
      self.p = p

  def addition(self, P1, P2):
      if P1 == INF_POINT:
          return P2
      if P2 == INF_POINT:
          return P1

      x1 = P1[0]
      y1 = P1[1]
      x2 = P2[0]
      y2 = P2[1]

      if self.equalModp(x1, x2) and self.equalModp(y1, -y2):
          return INF_POINT

      if self.equalModp(x1, x2) and self.equalModp(y1, y2):
          u = self.reduceModp((3 * x1 * x1 + self.a) *
                              self.inverseModp(2 * y1))
      else:
          u = self.reduceModp((y1 - y2) * self.inverseModp(x1 - x2))

      v = self.reduceModp(y1 - u * x1)
      x3 = self.reduceModp(u * u - x1 - x2)
      y3 = self.reduceModp(-u * x3 - v)

      return (x3, y3)

  #Fonction d'aide auxiliaires

  #cette méthode calcule le reste de la division de x
  def reduceModp(self, x):
      return x % self.p

  def equalModp(self, x, y):
      return self.reduceModp(x - y) == 0

  #cette méthode calcule l'inverse de x modulo p.
  def inverseModp(self, x):
      for y in range(self.p):
          if self.equalModp(x * y, 1):
              return y
      return None

  def multiplyByScalar(self, scalar, P):
      xTmp, yTmp = self.addition(P, P)
      count = 2
      while(count < scalar):
          xTmp, yTmp = self.addition((xTmp, yTmp), P)
          count += 1
      return xTmp, yTmp

#Test de fonction
ec = EllipticCurve(s,t,p)
yG = 2802
xG = 17
G=(xG,yG)
x_aG = 6179 
y_aG = 5635
bG = (9557,9197)

x_abG , y_abG = ec.multiplyByScalar(a, bG)
print("x_abG = ", x_abG )
print("y_abG = ", y_abG)

#x_abG =  1098
#y_abG =  6699
#abG(1098,6699)


# message clair de Bob
x_abG = 1098
encrypted_message = binascii.unhexlify('a6caa5d096cfad3206d6a5bced055d29de27057df32f6ff1c33a4732c06ace9f5f25758849ee1a1a3fc8b13be4d43e8be8f7792a4c52c386cbc693552660175857921937c0b24c82c067373e0e3e55db')
key_bytes = x_abG.to_bytes(16, byteorder='big', signed=False)

# Vecteur d'initialisation
iv = 0

# Conversion du vecteur en 16 octet (128 bits)
iv_bytes = iv.to_bytes(16, byteorder='big', signed=False)
cipher = AES.new(key_bytes, AES.MODE_CBC, iv_bytes)

# Dechiffrement du message
decrypted_message = cipher.decrypt(encrypted_message)

# Conversion de chaque octet du message chiffré en caractère
plainTextMessage = ''.join(map(chr, decrypted_message))
print(f"Message dechiffré : {plainTextMessage}")

#Message dechiffré : Rendez-vous le 3/1/2022 a 9h00 sur le parvis de la cathedrale de Strasbourg     




#Message altéré : Rendez-vous le 3/1/2022 a 8h00 sur le parvis de la cathedrale de Strasbourg 


message = "Rendez-vous le 3/1/2022 a 8h00 sur le parvis de la cathedrale de Strasbourg"
message_bytes = bytes(message, "utf-8")
message_length = len(message_bytes)

# Calculez le nombre de bytes nécessaires pour remplir
padding_length = 16 - (message_length % 16)
padding = bytes([0x00] * padding_length)

message_bytes_padded = message_bytes + padding

cipher = AES.new(key_bytes, AES.MODE_CBC, iv_bytes)
ciphertext = cipher.encrypt(message_bytes_padded)

# Convertissez le message chiffré en hexadécimal
ciphertext_hex = ciphertext.hex()
print("messsage altéré chiffré : ", ciphertext_hex)


#messsage altéré chiffré : 166,202,165,208,150,207,173,50,6,214,165,188,237,5,93,41,134,215,100,32,132,16,152,41,160,246,193,252,199,112,139,147,175,32,60,77,108,169,253,189,0,200,227,191,49,57,81,241,57,60,253,105,8,73,106,207,185,17,226,109,171,55,249,163,172,14,170,148,37,215,112,224,240,240,158,134,206,116,109,61
#message_Hexa = 'a6caa5d096cfad3206d6a5bced055d2986d7642084109829a0f6c1fcc7708b93af203c4d6ca9fdbd00c8e3bf313951f1393cfd6908496acfb911e26dab37f9a3ac0eaa9425d770e0f0f09e86ce746d3d'


def splitInto3BytesChunks(n):
    chunks = []
    while n > 0:
        n, remainder = divmod(n, 2 ** 24)
        chunks.append(remainder)
    return chunks

#Cette fonction permet de chiffrer une liste de nombres pesant chacun trois octets. retourne la liste des nombres chiffrés

def rsaEncrypt(clearMessage, d, n):
    encrytedMessage = []
    for threeBytes in clearMessage:
        cryptedBytes = pow(threeBytes, d, n)
        encrytedMessage.append(cryptedBytes)
    return encrytedMessage


clearMessageAltered = "Rendez-vous le 3/1/2022 a 8h00 sur le parvis de la cathedrale de Strasbourg"

#Cree l'objet hash SHA256
hastObject = hashlib.sha256()
# Le message Hash
hastObject.update(clearMessageAltered.encode('utf-8'))

hexHash = hastObject.hexdigest()

# On rajoute l'octet nul à la fin
hexHash += "00"
print(f"\nle hash du message clair alteré en decimal avec un octet nul rajouté à la fin : \n  {hexHash}\n")

# Conversion en nombre decimal le hash du message clair et alteré.
decimalHash = int("0x" + hexHash, 16)
print(f"\nle hash du message clair alteré en decimal : \n  {decimalHash}\n")

list3Bytes = splitInto3BytesChunks(decimalHash)
list3Bytes.reverse()
print(f"le hash precedent mais subdiviser en une liste de 11 nombre pesant chacun trois octets :\n {list3Bytes}\n")

print(f"La liste du message alteré chiffrer est : \n {rsaEncrypt(list3Bytes, 2042319124, 2517761299)}")


#[1975551207, 2184445872, 1657830182, 1911402412, 1338918093, 2388886091, 2269037333, 755923098, 1309864426, 1316222116, 2092762327]