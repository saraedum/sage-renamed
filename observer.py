# coding=utf-8

from timer import RepeatedTimer
from threading import RLock
import sys

class Observer(object):
    def __init__(self, thread_id, long_time=30):
        if thread_id not in sys._current_frames():
            raise ValueError
        self._thread_id = thread_id
        self._last = []
        self._last_complaint = 0
        self._status = [Observer.Context(self, "<uninitialized>")]
        self._status[0]._clock = 2**30
        self._timer = RepeatedTimer(5, self.check)
        self._long_time = long_time
        self._lock = RLock()

    def start(self):
        self._timer.start()

    def stop(self):
        self._timer.stop()

    class Context(object):
        def __init__(this, self, status):
            import time
            this._self = self
            this._status = status
            this._clock = time.clock()

        def __enter__(this):
            this._self._push(this)
            return this

        def __exit__(this, type, value, tb):
            this._self._pop(this)

    class Report(Context):
        def __enter__(this):
            this._self.log(this._status, color="white")
            return Observer.Context.__enter__(this)

    class Question(Report):
        def __init__(this, self, question, required_answer=None):
            Observer.Context.__init__(this, self, question)
            this._required_answer = required_answer
            this._received_answer = None

        def answer(this, answer):
            if this._required_answer is not None:
                assert this._required_answer == answer
            this._received_answer = answer
            return answer

        def __exit__(this, type, value, tb):
            if this._received_answer is None:
                this._self.log("→ ?", color="red")
            elif this._received_answer is True:
                this._self.log("→ yes.", color="green")
            elif this._received_answer is False:
                this._self.log("→ no.", color="red")
            else:
                this._self.log("→ %s"%this._received_answer, color="green")
            Observer.Report.__exit__(this, type, value, tb)

    def ask(self, question, required_answer=None):
        return Observer.Question(self, question, required_answer)

    def report(self, status):
        return Observer.Report(self, status)

    def _push(self, context):
        self._status.append(context)

    def _pop(self, context):
        assert self._status[-1] is context
        self._status.pop()

    def log(self, msg, color=None):
        msg = str(msg)
        with self._lock:
            if msg[-1]=="!":
                if color == "white":
                    color = "red"
                    msg = "\n"+msg
                elif color is None:
                    color = "white"
                msg = msg[:-1]+"."
            
            import sys
            if color == "red":
                sys.stdout.write("\x1b[31m")
            elif color == "green":
                sys.stdout.write("\x1b[32m")
            elif color == "white":
                sys.stdout.write("\x1b[37;1m")
            else:
                pass
            try:
                print " "*(len(self._status)-1) + str(msg)
            finally:
                sys.stdout.write("\x1b[0m")

    def _linearize_stack(self, stack):
        ret = []
        while stack is not None:
            ret.append(stack)
            stack = stack.f_back
        ret.reverse()
        return ret

    def _compare_frame(self, a, b):
        return a is b

    def check(self):
        try:
            stack = self._linearize_stack(sys._current_frames()[self._thread_id])
            common_ancestor = None
            new_last = []
            for last, current in zip(self._last, stack):
                last, when = last
                if self._compare_frame(last,current):
                    common_ancestor = last, when
                    new_last.append((last,when))
                else:
                    break
            import time
            NOW = time.clock()
            for current in stack[len(new_last):]:
                new_last.append((current,NOW))
            self._last = new_last

            if NOW-self._last_complaint < self._long_time:
                return
            if NOW-self._status[-1]._clock > self._long_time:
                with self._lock:
                    self.log("[long running computation] since %3ds: %s"%(NOW-self._status[-1]._clock,self._status[-1]._status))
                    self._last_complaint = NOW
                    if common_ancestor:
                        import traceback
                        self.log(traceback.format_stack(common_ancestor[0],1)[0])
        except:
            self.stop()
            raise
