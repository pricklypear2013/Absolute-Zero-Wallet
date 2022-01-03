#! /usr/bin/env python
# -*- coding: utf-8 -*-

# Converts dice rolls string (ex: 4162416241541356...) to electrum mnemonic
# word seed list and creates master public key for read-only wallet. Can
# optionally further encrypt the seed based on a user entered password.
#
# Also can create a temporary wallet for signing transactions using menomic
# word seed list (and optional password). Wallet key is encrypted with a
# generated random password and deleted after transaction is signed, to
# prevent leaking of private seed information.
#
# Copyright (C) 2014-2021 PricklyPear2013. All rights reserved.
#
# mnemonic word list code copied from Electrum 1.9.8
#
# Note even though I have upgraded to electrum 2+, I am still using the
# old/legacy (v1.9) wallet format. Upgrading to the new wallet format will
# require using the new BIP32 mnemonics. If changed then all funds would
# need to be moved over to a new wallet (with a new master key). Thomas has
# guaranteed that newer versions of Electrum will be able to use the older
# seeds and mnemonics for restoring wallets, so keeping the funds in the
# legacy wallet should be okay for the forseeable future.

############
# Creating private seed / mnemonic seed word list, master public key, and addresses with dice:
#
#   • Remove rPi from network, remove WiFi dongle, and use USB keyboard (not wireless).
#   • Run absolutezero program to convert dice roll results into keys (use 'c' to create new seed):
#
#       cd ~/btc/absolutezerowallet/
#       ./absolutezero
#
#    1) Place 5 casino dice in shoebox. Shake vigorously for 5 seconds. Tilt box to let dice line up on a side.
#    2) Read dice results left to right and enter numbers 1 to 6 with no spaces into absolutezero.
#    3) Repeat 10 times for a total of 50 roll results.
#    4) Write down the 12 private key words (optionally copy down private hex hash).
#    5) Double check key words copied down match display.
#
#   Optional steps to encrypt seed based on user entered password:
#
#    6) Re-run absolutezero to create password transformed version of the private seed.
#    7) Press 'c' then RETURN to enter Mnemonic Seed mode.
#    8) Enter 12 private key words from step #4.
#    9) Press RETURN and enter private password (memorized or writteon on paper)
#   10) Write down on *different* paper the 12 private key words (optionally copy down private hex hash).
#   11) Repeat steps #6 to #10 to verify same key words are shown.
#   12) Destroy paper from step #10 -- it was only used to verify password.
#
#   Result will be a file that is accessible when memory card is mounted on desktop:
#
#       /xfer/public-keys-and-addresses.txt
#
#   that has the master public keys and the first few deposit addresses for both wallets (with and without
#   password applied to seed). Either manually copy the keys over, or remove memory card and mount on
#   desktop to copy file.

############
# Restoring wallet and signing transaction with offine wallet:
#
#    1) Create the unsigned transaction on the connected desktop using Electrum.
#    2) Save resulting json file (unsigned.txn), which has a "hex" key, to rPi memory card:
#
#       /xfer/unsigned.txn      (filename is important)
#       /xfer/unsigned1.txn
#       /xfer/unsigned2.txn
#       ...
#
#    3) Remove rPi from network, remove WiFi dongle, and use USB keyboard (not wireless).
#    4) Run absolutezero program to create temporary wallet for signing based on mnemonic and private password:
#
#       cd ~/btc/absolutezerowallet/
#       ./absolutezero
#
#    5) Press 's' to enter sign transaction mode.
#    6) Enter 12 private key words (from step #10 above).
#    7) Press RETURN and enter private password.
#
#   Result will be a file(s) that is accessible when memory card is mounted on desktop:
#
#       /xfer/signed-success.txn
#
#   that can then be sent as a manual transaction from an online Electrum client. To copy, remove memory
#   card and mount on desktop.

############
# ** POTENTIAL PROBLEM **
#
# Electrum checks for transactions in addresses when building the wallet and stops adding new addresses
# after N (5 by default?) zero transaction addresses are found. We therefore might run into a problem
# when trying to sign transactions for addresses further down in our wallet. This is because Electrum
# will be air-gapped and not able to perform a sync to see any transactions (thus stopping before it is
# really at unused addresses). If this occurs then we need a way to build the wallet with additional
# addresses automatically as wallet "electrum restore" time. There isn't (as of 2.8) an argument to
# increase that address gap limit, but maybe it is a preference or we can just hack the source code.
# Note there is a python console commands "wallet.create_new_address(True and False)" that will add
# addresses to wallet beyong the gap limit:
#
#       https://bitcointalk.org/index.php?topic=1960859.0
#
# but the electrum python console is only available via the GUI.
#
# Update: I've read that it won't be a problem signing transactions even if the address is past the
# gap limit. That is the offline wallet will be able to sign the transactions even if they are beyond
# its gap limit of known addresses, so this shouldn't be a problem at all.

import ctypes
import fcntl
import hashlib
import json
import os
import sys
import termios
import time

from pymods import myutils as mu
from pymods import pexpect      # used to call into electrum
from traceback import format_exc

# ctypes hack from:
#       http://jonhnet.livejournal.com/
ctypes.CDLL("/opt/vc/lib/libbcm_host.so", mode=ctypes.RTLD_GLOBAL)
ctypes.CDLL('/usr/local/lib/libSDL2.so')
ctypes.CDLL('/usr/local/lib/libSDL2_ttf.so')
import sdl2.ext as sdl2ext
import sdl2.sdlttf as sdlttf
import sdl2

# electrum/lib/ copies:
import mnemonic, ecdsa, account, bitcoin

#################################################
kEntropyInfo = {
    'minDiceRolls': 50,     # math.log(6**50, 2) gives us 128 bits of entropy
    'targetEntropyBits': 128,
    'targetEntropyHex': 32
}
#   'minDiceRolls': 65,     # math.log(6**65, 2) gives us 168 bits of entropy
#   'targetEntropyBits': 160,
#   'targetEntropyHex': 40
#
#   'minDiceRolls': 100,    # math.log(6**100, 2) gives us 258 bits of entropy
#   'targetEntropyBits': 258,
#   'targetEntropyHex': 64

kNumAddressesToShow = 5     # Just enough so that we can compare with offline wallet.
kUseBIP32Wallet = False     # For Electrum 1.9.x we must use older non-BIP32 wallet format.
                            # See note at top of file on why this is still False.

kElectrumPath = "/home/btc/electrum/electrum"
kTempWalletPath = "/home/btc/private-wallet"   # runtime only (and encrypted)

kDataFolder = "/xfer"
kPublicLogFile = "public-keys-and-addresses.txt"

kTxnFileExtension = ".txn"
kUnsignedTxnFileBase = "unsigned"
kSignedTxnFile_success = "signed-success"
kSignedTxnFile_failure = "signed-failure"

#################################################
kBlack      = sdl2.SDL_Color(  0,   0,   0)
kDarkGray   = sdl2.SDL_Color( 64,  64,  64)
kMediumGray = sdl2.SDL_Color(128, 128, 128)
kLightGray  = sdl2.SDL_Color(191, 191, 191)
kWhite      = sdl2.SDL_Color(255, 255, 255)
kRed        = sdl2.SDL_Color(255,   0,   0)
kGreen      = sdl2.SDL_Color(  0, 255,   0)
kBlue       = sdl2.SDL_Color(  0,   0, 255)

kAlignLeft            = 0
kAlignCenter          = 10
kAlignCenterIfOneLine = 11
kAlignRight           = 20

kDisplayHeaderColor     = sdl2.SDL_Color(179, 255, 153)
kDisplayAllGoodColor    = sdl2.SDL_Color(179, 153, 255)
kDisplayErrorColor      = sdl2.SDL_Color(255,  38,  38)

#################################################
randomSeed = lambda n: "%032x" % ecdsa.util.randrange(pow(2,n))

def debugLog(logstr):
    pass
    #print(logstr)

def consoleLog(logstr):
    try:
        with open('/dev/console', 'a') as console:
            console.write(logstr + '\n')
    except:
        print("failed to write to /dev/console")

def grabFramebuffer():
    try:
        mu.callscript2(['/bin/con2fbmap', '1', '0'])
    except:
        print("failed to grab framebuffer")
        print(format_exc())

def releaseFramebuffer():
    try:
        mu.callscript2(['/bin/con2fbmap', '1', '1'])
    except:
        print("failed to release framebuffer")
        print(format_exc())

def electrumRestore(randomPassword, privateSeedHex):
    #       CAREFUL - for debugging only - logs private seed to console/file!
    # logfile = sys.stdout
    # logfile = open('../debuglog_restore.txt', 'w')
    logfile = None
    try:
        if os.path.exists(kTempWalletPath):
            os.remove(kTempWalletPath)
        # "electrum restore"
        args = ["restore", "-o", "-P", "-w%s" % kTempWalletPath, privateSeedHex]
        child = pexpect.spawn(kElectrumPath, args, logfile=logfile, timeout=600)
        print(". restoring wallet")

        child.expect('[pP]assword.*:')
        if randomPassword is not None:
            child.sendline(randomPassword)
            child.expect('[cC]onfirm.*:')
            child.sendline(randomPassword)
        else:
            child.sendline('')
        child.expect(pexpect.EOF)
        child.close(False)

        if child.exitstatus == 0 and child.signalstatus == None:
            print(". restore complete")
        else:
            print(". restore failed")
    except:
        # Don't log this exception, we already directed output from the
        # command to stdout which should explain why it failed.
        #
        # print("electrum restore failed")
        # print(format_exc())
        pass
    finally:
        if logfile is not None and logfile != sys.stdout:
            logfile.close()

def electrumStart(randomPassword):
    # CAREFUL - for debugging only - logs private seed to console/file!
    #
    # logfile = sys.stdout
    # logfile = open('../debuglog_signraw.txt', 'w')
    logfile = None
    try:
        # Yuck. New to Electrum 2.8.3 we have to start the daemon and load_wallet
        # before we can sign the transaction:
        #
        #      https://bitcointalk.org/index.php?topic=1964205.msg19524479
        #
        # "electrum daemon start"
        args = ["daemon", "start", "-P"]
        child = pexpect.spawn(kElectrumPath, args, logfile=logfile, timeout=600)
        child.close(False)

        # "electrum daemon load_wallet"
        args = ["daemon", "load_wallet", "-P", "-w%s" % kTempWalletPath]
        child = pexpect.spawn(kElectrumPath, args, logfile=sys.stdout, timeout=600)
        print(". loading wallet")
        # Documentation says that password is needed to open encrypted wallets, but
        # Electrum 2.8.3 isn't prompting me for one...
        #
        # if randomPassword is not None:
        #     child.expect('[pP]assword.*:')
        #     child.sendline(randomPassword)
        child.close(False)
    except:
        # Don't log this exception, we already directed output from the
        # command to stdout which should explain why it failed.
        #
        # print("electrum restore failed")
        # print(format_exc())
        pass
    finally:
        if logfile is not None and logfile != sys.stdout:
            logfile.close()

def electrumStop():
    logfile = None
    try:
        # "electrum daemon close_wallet"
        args = ["daemon", "close_wallet", "-P", "-w%s" % kTempWalletPath]
        child = pexpect.spawn(kElectrumPath, args, logfile=sys.stdout, timeout=600)
        print(". closing wallet")
        child.close(False)

        # "electrum daemon stop"
        args = ["daemon", "stop", "-P"]
        child = pexpect.spawn(kElectrumPath, args, logfile=logfile, timeout=600)
        child.close(False)
    except:
        # Don't log this exception, we already directed output from the
        # command to stdout which should explain why it failed.
        #
        # print("electrum restore failed")
        # print(format_exc())
        pass
    finally:
        if logfile is not None and logfile != sys.stdout:
            logfile.close()

def electrumSignRaw(randomPassword, txnData):
    outData = {'complete':False}
    # CAREFUL - for debugging only - logs private seed to console/file!
    #
    # logfile = sys.stdout
    # logfile = open('../debuglog_signraw.txt', 'w')
    logfile = None
    try:
        # "electrum signtransaction"
        args = ["signtransaction", "-P", "-w%s" % kTempWalletPath, txnData["hex"]]
        child = pexpect.spawn(kElectrumPath, args, logfile=logfile, timeout=600)
        print(". signing transaction")

        if randomPassword is not None:
            child.expect('[pP]assword.*:')
            child.sendline(randomPassword)
        child.expect(pexpect.EOF)
        child.close(False)

        if child.exitstatus == 0 and child.signalstatus == None:
            outData = json.loads(child.before)
            print(". signing complete")
        else:
            print(". signing failed")
    except:
        # Don't log this exception, we already directed output from the
        # command to stdout which should explain why it failed.
        #
        # print("electrum restore failed")
        # print(format_exc())
        pass
    finally:
        if logfile is not None and logfile != sys.stdout:
            logfile.close()
    return outData

#################################################
class KeyEvents(object):
    ########################################
    def __init__(self):
        self.fd = sys.stdin.fileno()
        self.oldflags = fcntl.fcntl(self.fd, fcntl.F_GETFL)
        self.oldattrs = termios.tcgetattr(self.fd)

        attrs = list(self.oldattrs)
        # iflag
        attrs[0] &= ~(termios.IGNBRK | termios.BRKINT | termios.PARMRK | termios.ISTRIP | termios.INLCR | termios.IGNCR | termios.ICRNL | termios.IXON)
        # oflag not adjusted (attrs[1] &= ~termios.OPOST)
        # cflag
        attrs[2] &= ~(termios.CSIZE | termios. PARENB)
        attrs[2] |= termios.CS8
        # lflag
        attrs[3] &= ~(termios.ECHONL | termios.ECHO | termios.ICANON | termios.ISIG | termios.IEXTEN)
        termios.tcsetattr(self.fd, termios.TCSANOW, attrs)
        # and turn off non-blocking
        fcntl.fcntl(self.fd, fcntl.F_SETFL, self.oldflags & ~os.O_NONBLOCK)

    def __del__(self):
        termios.tcsetattr(self.fd, termios.TCSAFLUSH, self.oldattrs)
        fcntl.fcntl(self.fd, fcntl.F_SETFL, self.oldflags)

    def nextKey(self):
        key = sys.stdin.read(1)
        if ord(key) == 3:       # Catch CNTRL-C
            raise KeyboardInterrupt
        return key

    def flushAllInput(self):
        termios.tcflush(sys.stdin, termios.TCIOFLUSH)

#################################################
class StatusDisplay(object):
    ########################################
    def __init__(self):
        grabFramebuffer()

        os.environ["SDL_VIDEODRIVER"] = "directfb"      # "fbcon"
        os.environ["SDL_FBDEV"] = "/dev/fb1"
        os.environ["SDL_DIRECTFB_LINUX_INPUT"] = "0"

        sdl2ext.init()              # sdl2.SDL_Init(sdl2.SDL_INIT_VIDEO)
        sdlttf.TTF_Init()

        winflags = sdl2.SDL_WINDOW_FULLSCREEN_DESKTOP | sdl2.SDL_WINDOW_BORDERLESS
        self.window = sdl2ext.Window("Absolute Zero Bitcoin Wallet", size=(10,10), position=(0,0), flags=winflags)
        self.windowSurface = self.window.get_surface()
        sdl2ext.fill(self.windowSurface, 0)
        self.refreshWindow()
        # self.window.maximize()    # Already maximized -- not needed.
        self.window.show()

        self.debugCount = 0
        (self.displayWidth, self.displayHeight) = self.window.size
        self.displayLeft = 0
        self.displayCenter = self.displayWidth / 2
        self.displayRight = self.displayWidth

        # sdlttf likes to return a bogus font object if the font requested doesn't exist,
        # and then will later crash if you try to use it. So make sure whatever fonts you
        # request do indeed exist on the system.
        #
        # /usr/share/fonts/truetype/ttf-dejavu/ installed fonts:
        #
        #   DejaVuSans.ttf, DejaVuSans-Bold.ttf
        #   DejaVuSerif.ttf, DejaVuSerif-Bold.ttf
        #   DejaVuSansMono.ttf, DejaVuSansMono-Bold.ttf

        normalSmallFont = sdlttf.TTF_OpenFont("/usr/share/fonts/truetype/ttf-dejavu/DejaVuSerif.ttf", 10)
        normalMediumFont = sdlttf.TTF_OpenFont("/usr/share/fonts/truetype/ttf-dejavu/DejaVuSerif.ttf", 11)
        normalLargeFont = sdlttf.TTF_OpenFont("/usr/share/fonts/truetype/ttf-dejavu/DejaVuSerif.ttf", 12)
        boldSmallFont = sdlttf.TTF_OpenFont("/usr/share/fonts/truetype/ttf-dejavu/DejaVuSerif-Bold.ttf", 10)
        boldMediumFont = sdlttf.TTF_OpenFont("/usr/share/fonts/truetype/ttf-dejavu/DejaVuSerif-Bold.ttf", 11)
        boldLargeFont = sdlttf.TTF_OpenFont("/usr/share/fonts/truetype/ttf-dejavu/DejaVuSerif-Bold.ttf", 12)
        self.defaultFont = normalSmallFont
        self.labelFont = normalSmallFont
        self.valueFont = boldSmallFont
        self.headerTypeFont = boldLargeFont
        self.descBodyFont = normalMediumFont
        
        self.defaultBgColor = kBlack
        self.defaultTextColor = kWhite
        self.defaultCaptionColor = kLightGray

        self.renderStatusStr = ""

        # also clear stdout console by forcing scroll
        print("\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n")

    def __del__(self):
        self.window = None
        sdlttf.TTF_Quit()
        sdl2ext.quit()

        releaseFramebuffer()

    ########################################
    def clearDisplay(self, refreshDisplay=False):
        sdl2ext.fill(self.windowSurface, 0)
        if refreshDisplay:
            self.refreshWindow()

    def refreshWindow(self):
        self.window.refresh()

    ########################################
    def _renderImage(self, imageFile, xpos, ypos):
        try:
            imageSurface = sdl2ext.load_image(imageFile)
            if imageSurface is None:
                print("status display could not find image file: " + str(imageFile))
                return
            srcrect = sdl2.SDL_Rect(0, 0, imageSurface.w, imageSurface.h)
            destrect = sdl2.SDL_Rect(xpos - imageSurface.w/2, ypos - imageSurface.h/2, imageSurface.w, imageSurface.h)
            sdl2.SDL_BlitSurface(imageSurface, srcrect, self.windowSurface, destrect)
            sdl2.SDL_FreeSurface(imageSurface)
        except:
            print(format_exc())

    ########################################
    def _renderTextRun(self, textStr, xpos, ypos, textColor, bgColor, font):
        destloc = sdl2.SDL_Rect(xpos, ypos)
        textSurface = sdlttf.TTF_RenderUTF8_Shaded(font, textStr.encode('utf8'), textColor, bgColor)
        sdl2.SDL_BlitSurface(textSurface, None, self.windowSurface, destloc)
        sdl2.SDL_FreeSurface(textSurface)

    def _renderText(self, textStr, pos, textColor=None, bgColor=None, font=None, align=kAlignLeft, wrap=True):
        if textColor is None:
            textColor = self.defaultTextColor
        if bgColor is None:
            bgColor = self.defaultBgColor
        if font is None:
            font = self.defaultFont

        (xorigin, yorigin) = pos
        if yorigin >= self.displayHeight:
            return      # starting position is off bottom of display -- bail out

        wrapwidth = 0
        forceLeftIfMultipleLines = False
        if align == kAlignLeft:
            wrapwidth = self.displayRight - xorigin
        elif align == kAlignRight:
            wrapwidth = xorigin - self.displayLeft
        elif align == kAlignCenter:
            wrapwidth = self.displayWidth
        elif align == kAlignCenterIfOneLine:
            align = kAlignCenter
            forceLeftIfMultipleLines = True
            wrapwidth = self.displayWidth

        if wrapwidth <= 0:
            return      # starting position is off left or right of display -- bail out

        try:
            if align == kAlignLeft and not wrap:
                # Simple case: left aligned and no wrap -- no text width calculation needed.
                self._renderTextRun(textStr, xorigin, yorigin, textColor, bgColor, font)
            else:
                lineheight = sdlttf.TTF_FontLineSkip(font)
                width_all = 0
                width_nsp = 0   # width minus whitespace characters on end of run
                charindex_all = 0
                minx = maxx = miny = maxy = advance = ctypes.c_long()
                ypos = yorigin
                textRemaining = textStr
                for singlechar in textStr:
                    isspace = (singlechar == " ")
                    sdlttf.TTF_GlyphMetrics(font, ord(singlechar), ctypes.byref(minx), ctypes.byref(maxx), ctypes.byref(miny), ctypes.byref(maxy), ctypes.byref(advance))
                    if wrap and width_all + advance.value > wrapwidth:
                        # we are wrapping -- render this line and continue measuring
                        if charindex_all == 0:
                            charindex_all = 1   # always render at least 1 character per line (avoid infinite looping)
                        if forceLeftIfMultipleLines:
                            align = kAlignLeft
                            xorigin = 0

                        if align == kAlignLeft:
                            xpos = xorigin
                        elif align == kAlignRight:
                            xpos = xorigin - width_nsp
                        elif align == kAlignCenter:
                            xpos = xorigin - width_nsp/2
                        self._renderTextRun(textRemaining[:charindex_all], xpos, ypos, textColor, bgColor, font)
                        textRemaining = textRemaining[charindex_all:]
                        width_all = advance.value
                        width_nsp = 0
                        if not isspace:
                            width_nsp = width_all
                        charindex_all = 1
                        ypos += lineheight
                        if ypos >= self.displayHeight:
                            return      # advanced past bottom of display -- bail out
                    else:
                        charindex_all += 1
                        width_all += advance.value
                        if not isspace:
                            width_nsp = width_all
                if charindex_all > 0:
                    if align == kAlignLeft:
                        xpos = xorigin
                    elif align == kAlignRight:
                        xpos = xorigin - width_nsp
                    elif align == kAlignCenter:
                        xpos = xorigin - width_nsp/2
                    self._renderTextRun(textRemaining[:charindex_all+1], xpos, ypos, textColor, bgColor, font)
        except:
            print(format_exc())

    def renderHeader(self, ypos, textStr):
        self._renderText(textStr, (self.displayCenter, ypos), font=self.headerTypeFont, textColor=kDisplayHeaderColor, align=kAlignCenter, wrap=False)

    def renderDesc(self, ypos, textStr):
        self._renderText(textStr, (self.displayCenter, ypos), font=self.descBodyFont, align=kAlignCenterIfOneLine, wrap=True)

    ########################################
    def _renderStatusFields(self):
        time_yalign = 135
        sdl2ext.fill(self.windowSurface, self.defaultBgColor, (0, time_yalign, self.displayRight, 26))
        self._renderText(self.renderStatusStr, (self.displayCenter, time_yalign), font=self.valueFont, align=kAlignCenterIfOneLine, wrap=True)
        self.refreshWindow()

    def updateStatusStr(self, statusStr):
        self.renderStatusStr = statusStr
        self._renderStatusFields()

#################################################
def getSeedFromMnemonics(display, keyinput):
    progress_yalign = 0
    display.clearDisplay()
    display.renderHeader(progress_yalign, "Mnemonic Seed")
    display.renderHeader(progress_yalign + 70, "Raw Hex Seed")
    progress_yalign += 15
    display.updateStatusStr("type mnemonic words")

    words_str = ""
    words_list= []
    seed_hex = ""
    while True:
        key = keyinput.nextKey()
        keyval = ord(key)
        if keyval >= 65 and keyval <= 90:
            keyval += 32    # force to lowercase
        elif keyval == 13:
            keyval = 32     # convert CR to space

        if keyval >= 97 and keyval <= 122:
            words_str += chr(keyval)
            display.renderDesc(progress_yalign, words_str)
            display.updateStatusStr("%d remaining" % (12 - len(words_list)))
            continue
        elif keyval != 32 and keyval != 127:
            display.updateStatusStr("key out-of-range")
            continue

        if keyval == 127:
            if len(words_str) > 0:
                words_str = words_str[:-1]
            sdl2ext.fill(display.windowSurface, display.defaultBgColor, (0, progress_yalign, display.displayRight, 55))
            sdl2ext.fill(display.windowSurface, display.defaultBgColor, (0, progress_yalign+70, display.displayRight, 55))
            display.renderDesc(progress_yalign, words_str)

        words_list = words_str.split()
        words_good = True
        for word in words_list:
            if word not in mnemonic.words:
                display.updateStatusStr("%s not valid" % (word))
                words_good = False
                break
        if words_good:
            try:
                seed_hex = mnemonic.mn_decode(words_list).upper()   # although we hash lowercase, we display uppercase
            except ValueError:
                display.updateStatusStr("invalid word entered")
                continue
            sdl2ext.fill(display.windowSurface, display.defaultBgColor, (0, progress_yalign+70, display.displayRight, 55))
            display.renderDesc(progress_yalign + 70, seed_hex)
            display.updateStatusStr("%d remaining" % (12 - len(words_list)))

            if keyval == 32 and words_str[-1:] != " ":
                if len(words_list) == 12:
                    break   # only break out if there are 12 words AND user hits space/return
                words_str += " "
    keyinput.flushAllInput()

    progress_yalign = 0
    display.clearDisplay()
    display.renderHeader(progress_yalign, "Seed Password")
    display.renderHeader(progress_yalign + 70, "Raw Hex Seed")
    progress_yalign += 15
    display.renderDesc(progress_yalign + 70, seed_hex)
    display.updateStatusStr(" enter seed password      or RTN to continue")

    password_str = ""
    protected_seed_hex = ""
    while True:
        key = keyinput.nextKey()
        keyval = ord(key)
        if not ((keyval >= 48 and keyval <= 57)
        or (keyval >= 65 and keyval <= 90)
        or (keyval >= 97 and keyval <= 122)
        or (keyval in [32, 13, 127])):
            display.updateStatusStr("key out-of-range")
            continue

        if ((keyval >= 48 and keyval <= 57)
        or (keyval >= 65 and keyval <= 90)
        or (keyval >= 97 and keyval <= 122)
        or (keyval == 32)):
            password_str += chr(keyval)
            display.renderDesc(progress_yalign, password_str)
        elif keyval == 127:
            if len(password_str) > 0:
                password_str = password_str[:-1]
            sdl2ext.fill(display.windowSurface, display.defaultBgColor, (0, progress_yalign, display.displayRight, 55))
            display.renderDesc(progress_yalign, password_str)
        else:   # keyval == 13
            break

        if len(password_str) > 0:
            runninghash = seed_hex.lower()   # Like electrum wallet, we always hash lowercase hex alpha chars.
            for char in password_str:
                src = runninghash + ":" + char
                runninghash = hashlib.sha256(src).hexdigest()
            protected_seed_hex = runninghash[:kEntropyInfo['targetEntropyHex']]
            protected_seed_hex = protected_seed_hex.upper()     # although we hash lowercase, we display uppercase
        else:
            protected_seed_hex = seed_hex
        sdl2ext.fill(display.windowSurface, display.defaultBgColor, (0, progress_yalign+70, display.displayRight, 55))
        display.renderDesc(progress_yalign + 70, protected_seed_hex)
        display.updateStatusStr("   continue entering        or RTN to complete")
    keyinput.flushAllInput()
    display.clearDisplay()

    if len(protected_seed_hex) > 0:
        seed_hex = protected_seed_hex
    return seed_hex

def getSeedFromDiceResults(display, keyinput):
    progress_yalign = 0
    display.clearDisplay()
    display.renderHeader(progress_yalign, "Dice Results")
    display.renderHeader(progress_yalign + 70, "Raw Hex Seed")
    progress_yalign += 15
    display.updateStatusStr("type dice roll results  or RTN for mnemonics")

    rolls_arg = ""
    rolls_normalized = ""
    while len(rolls_arg) < kEntropyInfo['minDiceRolls']:
        key = keyinput.nextKey()
        keyval = ord(key)
        if keyval == 13:
            return getSeedFromMnemonics(display, keyinput)
        elif keyval < 49 or keyval > 54:
            display.updateStatusStr("key out-of-range")
            continue

        rolls_arg += key
        rolls_normalized += chr(keyval - 1)
        rolls_int = int(rolls_normalized, 6) % 2**kEntropyInfo['targetEntropyBits']
        seed_hex = ("%X") % (rolls_int)

        display.renderDesc(progress_yalign, rolls_arg)
        sdl2ext.fill(display.windowSurface, display.defaultBgColor, (0, progress_yalign+70, display.displayRight, 55))
        display.renderDesc(progress_yalign + 70, seed_hex)
        display.updateStatusStr("%d remaining" % (kEntropyInfo['minDiceRolls'] - len(rolls_arg)))
    keyinput.flushAllInput()
    display.clearDisplay()

    # Recalc hex string a final time to force leading 0's.
    seed_hex = ("%0"+str(kEntropyInfo['targetEntropyHex'])+"X") % (rolls_int)
    return seed_hex

#################################################
if __name__ == '__main__':
    abspath = os.path.abspath(__file__)
    dname = os.path.dirname(abspath)
    os.chdir(dname)

    if not os.path.isdir(kDataFolder):
        raise Exception("Data folder %s must exist." % (kDataFolder))

    createPublicKey = False
    signTransaction = False
    unsignedTxnFileNames = []
    randomPassword = randomSeed(256)    # Runtime only password to encrypt wallet (restored wallets are single use)
    mpk = "-- unknown --"
    addresses = []
    keyinput = KeyEvents()
    display = StatusDisplay()
    display.updateStatusStr("starting")
    try:
        progress_yalign = 0
        display.clearDisplay()
        display.renderHeader(progress_yalign, "Absolute Zero")
        progress_yalign += 15
        display.renderHeader(progress_yalign, "Bitcoin Wallet")
        # Prompt user if they want to create a new master public key (no
        # private keys saved), or if they want to restore the electrum
        # wallet so they can sign the transaction offline (transaction
        # created online using a master public key read-only wallet).
        display.updateStatusStr("press C to create new   press S to sign txn")
        keyinput.flushAllInput()
        while True:
            key = keyinput.nextKey()
            keyval = ord(key)
            if keyval in [67, 99]:
                createPublicKey = True
                break
            elif keyval in [83, 115]:
                signTransaction = True
                break
            else:
                continue

        if createPublicKey:
            seed_hex = getSeedFromDiceResults(display, keyinput)
        elif signTransaction:
            # Any file matching the pattern unsigned*.txn will be used.
            for candidate in os.listdir(kDataFolder):
                candidatePath = os.path.join(kDataFolder, candidate)
                if not os.path.isfile(candidatePath):
                    continue
                basename, ext = os.path.splitext(candidate)
                if basename.startswith(kUnsignedTxnFileBase) and ext in [kTxnFileExtension]:
                    unsignedTxnFileNames.append(candidate)
            if len(unsignedTxnFileNames) < 1:
                raise Exception("No unsigned transaction files found (unsigned.txn, etc.).")
            seed_hex = getSeedFromMnemonics(display, keyinput)
        else:
            raise Exception("Aborting.");

        progress_yalign = 0
        display.renderHeader(progress_yalign, "Raw Hex Seed")
        progress_yalign += 15
        display.renderDesc(progress_yalign, seed_hex)
        display.refreshWindow()

        # Calc 12 mnemonic seed words.
        seed_hex = seed_hex.lower()    # Important: account.OldAccount.mpk_from_seed() needs lower case hex.
        seed_mnemonic = ' '.join(mnemonic.mn_encode(seed_hex))
        
        progress_yalign += 35
        display.renderHeader(progress_yalign, "Mnemonic Seed")
        progress_yalign += 15
        display.renderDesc(progress_yalign, seed_mnemonic)
        display.refreshWindow()

        # Validate by round tripping.
        seed_hextest = mnemonic.mn_decode(seed_mnemonic.split())

        debugLog('  hexified entropy1: %s' % (seed_hex))
        debugLog('  hexified entropy2: %s' % (seed_hextest))

        if seed_hex != seed_hextest:
            raise Exception("Validation failed decode equivalence test.");

        if createPublicKey:
            display.updateStatusStr("creating public key")
            if kUseBIP32Wallet:
                # New BIP32 wallet implementation. Not currently used -- untested!
                master_k, master_c, master_K, master_cK = bitcoin.bip32_init(seed_hex)
                k0, c0, K0, cK0 = bitcoin.bip32_private_derivation(master_k, master_c, "m/", "m/0'/")
                c0, K0, cK0 = bitcoin.bip32_public_derivation(c0.decode('hex'), K0.decode('hex'), "m/0'/", "m/0'/0")

                acct = account.BIP32_Account({ 'c':c0, 'K':K0, 'cK':cK0 })
            else:
                # Electrum 1.9.8 compatible mode (not BIP32).
                mpk = account.OldAccount.mpk_from_seed(seed_hex)
                acct = account.OldAccount({'mpk':mpk, 0:[], 1:[]})

            for i in range(kNumAddressesToShow):
                display.updateStatusStr("creating address %d" % (i+1))
                addresses.append(acct.create_new_address(0))

            display.updateStatusStr("finished")
            keyinput.flushAllInput()
            key = keyinput.nextKey()
        elif signTransaction:
            display.updateStatusStr("restoring wallet")
        else:
            display.updateStatusStr("aborted")
            keyinput.flushAllInput()
            key = keyinput.nextKey()
        del display
        del keyinput
    except Exception, e:
        del display
        del keyinput    # To avoid eaten <CR>'s we must del key input before printing to stdout.
        print("\n%s" % str(e))
        sys.exit(1)
    except:
        del display
        del keyinput    # To avoid eaten <CR>'s we must del key input before printing to stdout.
        print("Unknown Exception.")
        sys.exit(1)

    # The following takes place after the display and keyinput are deleted so that
    # the print() statements can format correctly.
    if createPublicKey:
        publicLogPath = os.path.join(kDataFolder, kPublicLogFile)
        with open(publicLogPath, 'a') as logFile:
            logFile.write("-------------------\n%s\n\n" % time.strftime("%Y-%m-%d %H:%M:%S", time.localtime()))
            logFile.write("Master Public Key:\n%s\n\n" % mpk)
            logFile.write("Public Addresses:\n")
            for addr in addresses:
                logFile.write("%s\n" % (addr))
            logFile.write("\n")
        print("\nPublic Key and Addresses logged to:\n%s" % (publicLogPath))
    elif signTransaction:
        try:
            print("\nRestoring and Signing\n")
            electrumRestore(randomPassword, seed_hex)
            electrumStart(randomPassword)

            resultFileNames = []
            for fileName in unsignedTxnFileNames:
                basename, ext = os.path.splitext(fileName)
                filePath = os.path.join(kDataFolder, fileName)
                with open(filePath) as txnFile:
                    txnData = json.load(txnFile)
                    outData = electrumSignRaw(randomPassword, txnData)
                    if outData.get('complete', False) is True:
                        resultFileName = "%s%s%s" % (kSignedTxnFile_success, basename[len(kUnsignedTxnFileBase):], kTxnFileExtension)
                    else:
                        resultFileName = "%s%s%s" % (kSignedTxnFile_failure, basename[len(kUnsignedTxnFileBase):], kTxnFileExtension)
                    signedTxnFilePath = os.path.join(kDataFolder, resultFileName)
                    with open(signedTxnFilePath, 'w') as signedTxnFile:
                        json.dump(outData, signedTxnFile)
                    resultFileNames.append(resultFileName)
            electrumStop()

            print("\nResults in %s/:" % (kDataFolder))
            for resultFileName in resultFileNames:
                print("%s" % (resultFileName))
        finally:
            # Finally delete the temp wallet file we had to create. Note
            # we encrypted the private key with a random seed, so the
            # fact this file may be hanging around on the flash card
            # in a recoverable state isn't too critical.
            if os.path.exists(kTempWalletPath):
                os.remove(kTempWalletPath)
